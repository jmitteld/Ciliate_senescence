program Telomere;
   {Telomerase rationing in protists as a means to enforce gene sharing. 2014Sept}
{$apptype CONSOLE}
{$N+,O-,J+,R+,E-,X+,V+}
{ define NEWSPLIT}
{ define NDEBUG}


{Many cells in a cartesian array, each of which can house several orgs (aim for <10). Each time
step, there is diffusion of food from 4 neighboring cells, and food deposited into each cell.
Concentration of food determines how much each org picks up, because we assume he filters at a constant rate.}

{When food reaches a certain threshold, the org can reproduce via mitosis. That threshold is its fitness. Small probability of mutation.
In mitosis, the genes have a small probability of mutating a small amount. But in conjugation, one gets much bigger, the other much smaller,
so there is opportunity for great gain via “best man” mechanism.

There is a cost of living that decreases reproduction when there is crowding. But crowding is relative to fitness.
Make the CoL proportional to repthresh, so the fitter orgs get a double benefit.
There is also a mortality per time step that prevents population from running away.
There is an energy cost of conjugation. Energy is split in half with mitosis.

Dynamic: the fulltelo evolves up without limit, allowing the horniness to evolve down without limit.
Then we’re in trouble. The ones with smaller fulltelo don’t have this problem, and so their horniness doesn’t evolve down,
so they share genes more often.}

{Note on double bookkeeping: Each org has [x,y] that identify its cell.  Each cell has an orglist indexing the numbers of the orgs living therein.  Whenever
 there is a birth or a death, bost lists must be updated.}

uses
  SysUtils,
  DOSSTUFF;

const {untyped} crlf=#13#10; maxorg=1500000; maxcap=2000; maxx=256; gridsiz=sqr(maxx); one:double=1.0; half:double=0.5; quarter:double=0.25; tiny:double=1.0E-9; large=1000; stoptime=20000;

      csvheader='  time, Norg,  Food, ';
      headerstr='   TIME   NORG    FOOD RpThrsh   RATIO    Telo   Horny Birth:Sex %Sen Clumpy Largst FdAdd';
      filext='008';

type
   org=record
     {state variables}
     energy :double;
     telomere :smallint; {reduced by 1 with each replication; restored}
     x,y      :word; {location}
     {genes}
     repthresh :double; {essentially its (inverse) fitness; it may be easier to store the log of this quantity}
     {fulltelo  :double; {how long are telomeres after conjugation}
     thegene :boolean; {if TRUE then telomere is lost with each replication}
     horniness :double; {this is the propensity to conjugate, per pair encounter. Product of two horniness numbers}
     end;

   cell = record
       norg   :word;  {number of orgs in this cell}
       orglist:array[1..maxcap] of integer; {list of org numbers for orgs in this cell, 1..norg, the rest are unused}
       food   :double; {concentration of food locally}
       end;

   agecase=(ALL,NONE,MIXED,SEPARATE,MUTABLE);

const {typed}  initcount=100000; irepthresh:double=1.0; ifulltelo:word=30; ihorniness:double=0.07; diffusion:double=0.2;  col:double=0.01;
      ifoodadded:double=0.1;   mutation:double=1E-4;  portion:double=0.1; {proportion of available food an org can eat in a time step}
      appetite=0.25; {25% of body weight is the max that can be absorbed in a time step}
      aging:agecase=SEPARATE;  discriminating:boolean=FALSE;  overflow:boolean=false;
      mort:double=0.03; splitmult:double=1.02;  conjcost:double=0.6;

var fin,fout,sumfile,csvfile                    :text;
    t,birthcount,conjcount                      :integer;
    splitstr,
    foutname,finname                            :string;
    s                                           :array[1..maxorg] of integer;
    o                                           :array[1..maxorg] of org;
    c                                           :array[0..maxx,0..maxx] of cell;
    avgrepthresh,avghorn,
    foodadded,outcome                           :double;
    gnorg                                       :integer;

procedure IntegrityCheck;
          var i,sumorg   :integer;
              y,x :word;
          begin
          sumorg:=0;
          for y:=1 to maxx do for x:=1 to maxx do sumorg:=sumorg+c[y,x].norg;
          if (gnorg<>sumorg) then writeln('sumorg=',sumorg,' but gnorg=',gnorg,'.');
          for y:=1 to maxx do for x:=1 to maxx do with c[y,x] do for i:=1 to norg do
             if (o[orglist[i]].y<>y) or (o[orglist[i]].x<>x) then writeln('Cell [',y,',',x,'] points to org[',orglist[i],'] with y=',o[orglist[i]].y,' and x=',o[orglist[i]].x,'.');
          end;

function ToText(a :agecase):string;
         begin
         case a of
           ALL : result:='ALL';
          NONE : result:='NONE';
         MIXED : result:='MIXED';
      SEPARATE : result:='SEPARATE';
       MUTABLE : result:='MUTABLE';
          end; end;

procedure OpenSummaryFile;
          const csvheader='Rate of chg, Init distrib, Intermarriage, Mort rate, SplitMult, ConjCost, time, Final %sen';
          begin
          assign(csvfile,'TELO-SUM.CSV');   {$I-} append(csvfile); {$I+} if (ioresult>0) then rewrite(csvfile);
          write(csvfile,DateTimeToStr(date+time),' Appetite limited ');
{$ifdef NEWSPLIT} writeln(csvfile,'NEW SPLIT'); {$else NEWSPLIT} writeln(csvfile,'OLD SPLIT'); {$endif NEWSPLIT}
          writeln(csvfile,csvheader);
          close(csvfile);
          end;

procedure OpenOutputFile;
          var defstr :string;
          begin
          defstr:='  ';
          assign(fout,foutname);   {$I-} append(fout); {$I+} if (ioresult>0) then rewrite(fout);
          assign(sumfile,'TELO-SUM.'+filext);   {$I-} append(sumfile); {$I+} if (ioresult>0) then rewrite(sumfile);
          write(fout,crlf,'TELOMERE ' + itoa(maxx)+'*'+itoa(maxx) + ' ' +DateTimeToStr(date+time) + ' ' + ToText(aging)+' '); if (not discriminating) then write(fout,'NOT_'); writeln(fout,'DISCRIMINATING');
          writeln(fout,'Init count=',initcount,'; Food added=',ifoodadded:5:3,
                  '; Init Full telo=',ifulltelo,'; Init rep thresh=',irepthresh:5:3,'; Init horniness=',ihorniness:5:3,'; diffusion=',diffusion:6:4,'; mortality=',mort:6:4,
                  '; mutation=',ftoa(mutation,5),'; splitmult=',splitmult:5:3,'; conjcost=',conjcost:5:3,'; portion=',portion:5:3);
          if (upcase(foutname[length(foutname)])='V') then writeln(fout,CSVheader) else writeln(fout,headerstr);
          writeln(headerstr);
          close(fout);
          end;

procedure Init;
          var i         :integer;
              x,y       :word;
          begin
          {$ifndef NDEBUG} randomize; {$endif NDEBUG}
          t:=0; birthcount:=0; conjcount:=0;
          gnorg:=initcount; outcome:=0.5; foodadded:=ifoodadded;
          for y:=1 to maxx do for x:=1 to maxx do with c[y,x] do begin
            norg:=0;
            food:=random*foodadded;
            end;

          for i:=1 to gnorg do with o[i] do begin
            repthresh:=irepthresh*(1+0.1*(random-random));
            energy:=repthresh*half*(1+random-random);
            {fulltelo:=round(ifulltelo*(1+random-random));}
            telomere:=round(ifulltelo*half*(1+random-random));
            horniness:=ihorniness*(1+random-random);
            x:=succ(random(maxx)); y:=succ(random(maxx));
            case aging of ALL : thegene:=TRUE;
                         NONE : thegene:=FALSE;
                MUTABLE,MIXED : thegene:= (random(2)=0);
                     SEPARATE : thegene:= (2*x>maxx);
                     end; {case}
            with c[y,x] do begin
              inc(norg);
              orglist[norg]:=i;
              end;
            end;
          foutname:='Telomere.'+filext;
          end; {Init}

procedure ComputeStats;
          var i,genesum   :integer;
              norg2sum    :comp;
              maxnorg,second,third,
              y,x     :word;
              clumpiness,
              birth2sexratio,
              avgtelo,avgfood          :double;
          begin
          IntegrityCheck;
          avgfood:=0;  avgrepthresh:=0; avgtelo:=0;  avghorn:=0; norg2sum:=0; maxnorg:=0; second:=0; third:=0; genesum:=0;
          for y:=1 to maxx do for x:=1 to maxx do with c[y,x] do begin
            avgfood:=avgfood+food;
            norg2sum:=norg2sum+sqr(norg);
            if (third<norg) then
              if (norg>=maxnorg)then begin third:=second; second:=maxnorg; maxnorg:=norg; end
              else if (norg>=second) then begin third:=second; second:=norg; end
              else third:=norg;
            end;
          avgfood:=avgfood/gridsiz;
          clumpiness:=norg2sum/gnorg; clumpiness:=log(clumpiness/gnorg);
          for i:=1 to gnorg do with o[i] do begin
            if (thegene) then inc(genesum);
            avgrepthresh:=avgrepthresh+o[i].repthresh;
            if (thegene) or (aging=NONE) then avgtelo:=avgtelo+telomere;
            avghorn:=avghorn+o[i].horniness;
            end;
          avgrepthresh:=avgrepthresh/gnorg; avghorn:=avghorn/gnorg;
          if (aging=NONE) then avgtelo:=avgtelo/gnorg else avgtelo:=avgtelo/genesum;
          if (conjcount>0) then birth2sexratio:=birthcount/conjcount else birth2sexratio:=large;
          outcome:=genesum/gnorg;
          birthcount:=0; conjcount:=0;
{          writeln(t:8,gnorg:8,avgfood:8:3,avgrepthresh:8:3,avgtelo:8:0,avghorn:8:3);}
          writeln(t:7,gnorg:7,log(avgfood):8:3,log(avgrepthresh):8:3,avgfood/avgrepthresh:8:3,avgtelo:8:0,avghorn:8:3,birth2sexratio:7:1,100*genesum/gnorg:7:2,'%',clumpiness:6:2,' ',maxnorg:5,foodadded:6:3);
          append(fout); writeln(fout,t:7,gnorg:7,log(avgfood):8:3,log(avgrepthresh):8:3,avgfood/avgrepthresh:8:3,avgtelo:8:0,avghorn:8:3,birth2sexratio:8:1,100*genesum/gnorg:7:2,'%',clumpiness:6:2,' (',maxnorg,',',second,',',third,')',foodadded:6:3);
          if (gnorg>100000) or (maxnorg>160) then begin
            foodadded:=foodadded*0.83;
            writeln(fout,'                                                  food added=',foodadded:9:7);
{            writeln('                                                  food added=',foodadded:9:7);}
            end;
          close(fout);
          end; {ComputeStats}

function Prev(x:word):word;
         begin
         result:=pred(x);
         if (result=0) then result:=maxx;
         end;

function Next(x:word):word;
         begin
         result:=succ(x);
         if (result>maxx) then result:=1;
         end;

procedure RandomVNNeighbor(y,x :word; var yy,xx :word); {von Neumann neighbor}
          begin
          yy:=y; xx:=x;
          case (random(4)) of
             0 : xx:=prev(x);
             1 : xx:=next(x);
             2 : yy:=prev(y);
             3 : yy:=next(y);
             end;
          end;
(*
procedure RandomNeighbor(y,x :word; var yy,xx :word);
          begin
          yy:=y; xx:=x;
          if (random(2)=0) then begin
            if (random(2)=0) then inc(yy) else dec(yy);
            if (yy=0) then yy:=xmax
            else if (yy>xmax) then yy:=1;
            end
          else begin
            if (random(2)=0) then inc(xx) else dec(xx);
            if (xx=0) then xx:=xmax
            else if (xx>xmax) then xx:=1;
            end;
          end;
*)
procedure Mutate(var u :double);
          var wr :double;
          begin
          wr:=exp((random-random)*mutation);
          u:=u*wr;
          end;
(*
procedure Split(var u,v :double);  {In conjugation}
          var wr :double;
          begin
          wr:=exp((random-one)*splitmult);
          u:=half*(u+v); v:=u;
          u:=u*wr; v:=v/wr;
          end;
(*
procedure Split(var u,v :double);  {In conjugation}
          var newu,newv :double;
          begin
          if (u<0) or (v<0) then begin write('Can''t split ',u:8:3,',',v:8:3); readln; end;
          newu:=u*exp(random*splitmult*ln(u/v));
          newv:=v*exp(random*splitmult*ln(v/u));
          u:=newu; v:=newv;
          end;
*)
{$ifdef NEWSPLIT}
procedure Split(var u,v :double);  {In conjugation}
          var newu,newv :double;
          begin
          newu:=u*exp((1-sqr(random))*splitmult*ln(v/u));
          newv:=v*exp((1-sqr(random))*splitmult*ln(u/v));
          u:=newu; v:=newv;
          end;
{$else NEWSPLIT}
procedure Split(var u,v :double);  {In conjugation}
          var wr :double;
          begin
          wr:=exp((random-one)*splitmult);
          u:=half*(u+v); v:=u;
          u:=u*wr; v:=v/wr;
          end;
{$endif NEWSPLIT}

procedure Mitosis(i :integer);
          const safetymargin=round(maxorg*0.99);
          var yy,xx :word;
          begin
          if (gnorg>safetymargin) then begin writeln('gnorg=',gnorg); writeln(fout,'gnorg=',gnorg); overflow:=true; exit; end;
          inc(birthcount);
          with o[i] do begin
            energy:=half*energy;
            if thegene then dec(telomere);
            RandomVNNeighbor(y,x,yy,xx);
            end;
          inc(gnorg);
          o[gnorg]:=o[i];
          with o[gnorg] do begin x:=xx; y:=yy; Mutate(repthresh); Mutate(horniness); end;
          with c[yy,xx] do
             if (norg=maxcap) then begin writeln('Overflow at site (',yy,',',xx,')'); dec(gnorg); overflow:=true; end
             else begin inc(norg); orglist[norg]:=gnorg; end;
          end;

procedure Conjugate(i,j :integer);
          begin
          if (discriminating) then if (o[i].thegene xor o[j].thegene) then exit;
          inc(conjcount);
          with o[i] do energy:=energy-repthresh*conjcost;
          with o[j] do energy:=energy-repthresh*conjcost;
          Split(o[i].repthresh,o[j].repthresh);
             if (o[i].repthresh<avgrepthresh*0.01) then o[i].repthresh:=avgrepthresh*0.01;
             if (o[j].repthresh<avgrepthresh*0.01) then o[j].repthresh:=avgrepthresh*0.01; {prevent runaway}
          {Split(o[i].fulltelo,o[j].fulltelo);}
          Split(o[i].horniness,o[j].horniness);
             if (o[i].horniness<avghorn*0.01) then o[i].horniness:=avghorn*0.01;
             if (o[j].horniness<avghorn*0.01) then o[j].horniness:=avghorn*0.01;
             if (o[i].horniness>avghorn*100) then o[i].horniness:=avghorn*100;
             if (o[j].horniness>avghorn*100) then o[j].horniness:=avghorn*100; {prevent runaway}
          with o[i] do if (telomere<round(ifulltelo)) then telomere:=round(ifulltelo);
          with o[j] do if (telomere<round(ifulltelo)) then telomere:=round(ifulltelo);
          end;

procedure DiffuseAndAddFood;
          var y,x :word;
              newfood :array[1..maxx,1..maxx] of double;
          begin
          for y:=1 to maxx do for x:=1 to maxx do
            newfood[y,x]:=(1-diffusion)*c[y,x].food + diffusion*quarter*(c[prev(y),x].food+c[next(y),x].food+c[y,prev(x)].food+c[y,next(x)].food);
          for y:=1 to maxx do for x:=1 to maxx do
            c[y,x].food:=newfood[y,x]+foodadded;
          end;

procedure Die(i :integer);  {this is a little complicated because of the double bookkeeping.  Not only do we remove o[i] from the global list, we also have to find the
                             cell he was in and delete i from the cell's orglist.  Then, after we promote o[norg] to compact the list, we have to find the cell where
                             o[norg] was in the orglist, and tell the cell that o[norg] is now to be called by the name o[i].}
          var j :word;
          begin
          with c[o[i].y,o[i].x] do begin
            j:=0; repeat inc(j) until (j>norg) or (orglist[j]=i);
            if (j>norg) then begin write('A norg=',norg,';  Bookkeeping error: org[',i,'] not found in cell [',o[i].y,',',o[i].x,']...'); readln; end;
            orglist[j]:=orglist[norg]; dec(norg);
            end;
          if (i=gnorg) then begin dec(gnorg); exit; end; {otherwise, compact the list}
          o[i]:=o[gnorg];
          with c[o[i].y,o[i].x] do begin
            j:=0; repeat inc(j) until (j>norg) or (orglist[j]=gnorg);
            if (j>norg) then begin write('B norg=',norg,';  Bookkeeping error: org[',i,'] not found in cell [',o[i].y,',',o[i].x,']...'); readln; end;
            orglist[j]:=i;
            end;
          dec(gnorg);
          end;

procedure ConjugationOpp951;
          var y,x :word;
              i,j :integer;
          begin
          for y:=1 to maxx do begin append(fout); write(fout,crlf,'y=',y);
            for x:=1 to maxx do with c[y,x] do begin
             {append(fout); write(fout,',',x); close(fout);} for i:= 1 to pred(norg) do
               for j:=succ(i) to norg do begin
                 if (random<o[orglist[i]].horniness*o[orglist[j]].horniness) then Conjugate(orglist[i],orglist[j]);
                 end;
              end; end;
          end;

procedure ConjugationOpp;
          var y,x :word;
              i,j :integer;
          begin
          for y:=1 to maxx do for x:=1 to maxx do with c[y,x] do
            for i:= 1 to pred(norg) do
              for j:=succ(i) to norg do begin
                if (random<o[orglist[i]].horniness*o[orglist[j]].horniness) then Conjugate(orglist[i],orglist[j]);
                end;
          end;

procedure Eat;
          var i :integer;
              lim1,lim2,foodeaten   :double;
          begin {use shuffled list, because order matters}
          for i:=1 to gnorg do
            with o[s[i]] do with c[y,x] do begin
            lim1:=food*portion;
            lim2:=energy*appetite;
            foodeaten:=lim1*lim2/(lim1+lim2);
            energy:=energy - col*repthresh + foodeaten;;
            food:=food-foodeaten;
            if (food<0) then food:=0;
            end;
          end;

procedure Reproduce; {don't need shuffled list because order doesn't matter}
          var i :integer;
          begin
          overflow:=false;
          for i:=1 to gnorg do
            with o[i] do
              if (energy>repthresh) then Mitosis(i);
          end;

procedure Cull;
          var i :integer;
          begin
          i:=1;
          while (i<=gnorg) do begin
            with o[i] do
              if (random<mort) or (telomere<=0) or (energy<=0) then Die(i) else inc(i);
            end;
          end;

procedure Shuffle;  {creates a shuffled list of numbers s[1..norg]}
          var i,j,k :integer;
          begin
          for i:=1 to gnorg do s[i]:=i;
          for i:=1 to gnorg do begin
            j:=succ(random(gnorg));
            k:=s[j];
            s[j]:=s[i];
            s[i]:=k;
            end;
          end;

procedure OnePeriod;
          begin
          ConjugationOpp;
          {$ifdef NDEBUG} IntegrityCheck; {$endif}
          DiffuseAndAddFood;
          {$ifdef NDEBUG} IntegrityCheck; {$endif}
          Shuffle;
          {$ifdef NDEBUG} IntegrityCheck; {$endif}
          Eat;
          {$ifdef NDEBUG} IntegrityCheck; {$endif}
          Reproduce;
          {$ifdef NDEBUG} IntegrityCheck; {$endif}
          Cull;
          {$ifdef NDEBUG} IntegrityCheck; {$endif}
          inc(t);
          if (t mod 200=0) then ComputeStats
          {else if (gnorg>100000) or (overflow) then begin foodadded:=foodadded*0.99; writeln('                       foodadded=',foodadded:5:3); end;}
          else if (gnorg>150000)or (overflow) then  begin foodadded:=foodadded*0.95; {writeln('                       foodadded=',foodadded:5:3);} end
          else if (gnorg>100000) then foodadded:=foodadded*0.99;
          end;

procedure OneRun;
          begin
          Init;
          IntegrityCheck;
          OpenOutputFile;
          repeat OnePeriod until (gnorg<5) or (t>=stoptime) or (outcome<0.07) or (outcome>0.93);
          append(sumfile);
          write(sumfile,crlf,'TELOMERE ' + itoa(maxx)+'*'+itoa(maxx) + DateTimeToStr(date+time) + ' ' + ToText(aging)); if (not discriminating) then write(sumfile,' NOT'); writeln(sumfile,' DISCRIMINATING');
          writeln(sumfile,'Init count=',initcount,'; Food added=',ifoodadded:5:3,
                  '; Init Full telo=',ifulltelo,'; Init rep thresh=',irepthresh:5:3,'; Init horniness=',ihorniness:5:3,'; diffusion=',diffusion:6:4,'; mortality=',mort:6:4,
                  '; mutation=',ftoa(mutation,5),'; splitmult=',splitmult:5:3,'; conjcost=',conjcost:5:3,'; portion=',portion:5:3);
          write(sumfile,'Outcome=',outcome:6:3,'  t=',t:6,'   ');
          close(sumfile);
          append(csvfile);
          {if (outcome>half) then write(csvfile,1000/t:6:3) else write(csvfile,-1000/t:6:3);}
          if (outcome>0.9) then write(csvfile,2) else if (outcome>0.6) then write(csvfile,1) else if (outcome>0.4) then write(csvfile,0) else if (outcome>0.1) then write(csvfile,-1) else write(csvfile,-2);
          writeln(csvfile,',',totext(aging),',',discriminating,',',mort:5:3,',',splitmult:5:3,',',conjcost:5:3,',',t,',',outcome:5:3);
          close(csvfile);
          end;

(*TELOMERE 256*256 10/5/2014 7:11:10 AM NONE NOT DISCRIMINATING
Init count=100000; Food added=0.100; Init Full telo=30; Init rep thresh=1.000; Init horniness=0.070; diffusion=0.2000; mortality=0.0100; mutation= 1.E-4;  conjcost=0.600; portion=0.100

   aging:=separate,mixed;
   discriminating:=true,false;
   mortality:=0.01,0.03,0.08;
   splitconst:=0.02,0.06,0.15;
   conjcost:=0.1,0.25,0.6;
   *)

   var i,k,l,m,z :integer;
       j:boolean;
const ad:array[0..1] of agecase=(MIXED,SEPARATE);
      mm:array[0..2] of double=(0.07,0.03,0.01);
{$ifdef NEWSPLIT}
      ss:array[0..2] of double=(1.2,1.4,1.70);  {for new Split func}
{$else NEWSPLIT}
      ss:array[0..4] of double=(0.05,0.1,0.2,0.4,0.8); {for old Split func}
{$endif NEWSPLIT}
      cc:array[0..3] of double=(1.5,0.6,0.25,0.1);

{Main}

begin
          (* Init;
          IntegrityCheck;
          OpenOutputFile;
          repeat OnePeriod until (gnorg<5) or (t>=stoptime) or (outcome<0.01) or (outcome>0.99);
          write('DONE...'); readln;
          end. *)

z:=0;
repeat
OpenSummaryFile;
for i:=1 downto 0 do for j:=true downto false do for k:=0 to 2 do for l:=0 to 2 do for m:=0 to 3 do begin
  aging:=ad[i]; discriminating:=j; mort:=mm[k]; splitmult:=ss[l]; conjcost:=cc[m];
  inc(z);
  if (z>39) then OneRun;
  end;
until false;  
end.
