{What is the simplest system that guarantees the necessity of conjugation?
Aa and Bb
Four catastrophes wipe out AB, Ab, aB and ab, successively.  Unless genes have been mixed in the interim, that's everyone.
You don't need diploid genetics.  Each org has just nC=2 genes and conjugation crosses them over. }


program Telomere2m;
   {Telomerase rationing in protists as a means to enforce gene sharing. 2014Sept}
{$apptype CONSOLE}
{$N+,O-,J+,R+,E-,X+,V+}
{ define NDEBUG}
{ define CONTAGION}
{$define MEANSITE}

uses
  SysUtils,
  DOSSTUFF;

const {untyped} crlf=#13#10; maxorg=1000000; maxcap=2000; maxx=128; gridsiz=sqr(maxx); one:double=1.0; half:double=0.5; quarter:double=0.25;
      twotothe :array[0..7] of byte=(1,2,4,8,16,32,64,128);  tiny:double=1.0E-9; large=1000; stoptime=20000;

      csvheader='Time,Norg,Food,Telo,Horny,Birth:Sex,%Sen,Clumpy,Largest,%Vulner,AvgDivers';
      headerstr='   TIME   NORG   Food Telo   Horny Birth:Sex %Sen Clumpy Largst %Vulner  AvgDivers';
      filext='001';  nC=2; {types of catastrophe genes} maxgene=3; maxgenep=1+maxgene; {2^nC}  catfreq:double=0.13;  immunitycost=1.5;

type
   immgenes=byte; {fingerprint that determines resistance to each kind of catastrophe.  A byte will hold 8 genes of two alleles each.  We start with just 2.}

   org=object
     {state variables}
     energy :double;
     telomere :smallint; {reduced by 1 with each replication; restored}
     x,y      :word; {location}
     {genes}
     thegene :boolean; {if TRUE then telomere is lost with each replication}
     horniness :double; {Product of two horniness numbers is the propensity to conjugate, per pair encounter; except that MEANSITE standardizes the number of pair encounters.}
     immunity :immgenes;
     end;

   site = record
       norg   :word;  {number of orgs in this site}
       orglist:array[1..maxcap] of integer; {list of org numbers for orgs in this site, 1..norg, the rest are unused}
       food   :double; {concentration of food locally}
       end;

   agecase=(ALL,NONE,MIXED,SEPARATE,MUTABLE);

const {typed}  initcount=200000; repthresh:double=1.0; fulltelo=30; ihorniness=0.005; foodretention=0.8; {20% of uneaten food spoils in each timestep} diffusion=0.2;  col=0.01;
      foodadded=0.70;   mutation:double=1E-4;  portion:double=0.1; {proportion of available food an org can eat in a time step}
      appetite=0.25; {when food is abundant, individual can eat at most 1/4 of its weight in a time step} aging:agecase=NONE;  discriminating:boolean=FALSE;  overflow:boolean=false;     mutprob=3E-8;   inviscosity=0.1;
      mort=0.05;   conjcost:double=0.1;  DomRec:array[false..true] of string=('REC','DOM');

var fin,fout,sumfile,csvfile                    :text;
    t,birthcount,conjcount                      :integer;
    splitstr,
    foutname,finname                            :string;
    s                                           :array[1..maxorg] of integer;
    o                                           :array[1..maxorg] of org;
    c                                           :array[0..maxx,0..maxx] of site;
    avghorn,
    outcome                                     :double;
    gnorg                                       :integer;

procedure IntegrityCheck;
          var i,sumorg   :integer;
              y,x :word;
          begin
          sumorg:=0;
          for y:=1 to maxx do for x:=1 to maxx do sumorg:=sumorg+c[y,x].norg;
          if (gnorg<>sumorg) then writeln('sumorg=',sumorg,' but gnorg=',gnorg,'.');
          for y:=1 to maxx do for x:=1 to maxx do with c[y,x] do for i:=1 to norg do
             if (o[orglist[i]].y<>y) or (o[orglist[i]].x<>x) then writeln('Site [',y,',',x,'] points to org[',orglist[i],'] with y=',o[orglist[i]].y,' and x=',o[orglist[i]].x,'.');
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
          const csvheader='Rate of chg, Init distrib, Intermarriage, Mort rate, ConjCost, time, Final %sen';
          begin
          assign(csvfile,'TELO-SUM.CSV');   {$I-} append(csvfile); {$I+} if (ioresult>0) then rewrite(csvfile);
          write(csvfile,DateTimeToStr(date+time),' ');
{$ifdef NEWSPLIT} writeln(csvfile,'NEW SPLIT'); {$else NEWSPLIT} writeln(csvfile,'OLD SPLIT'); {$endif NEWSPLIT}
          writeln(csvfile,csvheader);
          close(csvfile);
          end;

procedure OpenOutputFile;
          var defstr :string;
          begin
          defstr:='  ';
          assign(fout,foutname);   {$I-} append(fout); {$I+} if (ioresult>0) then rewrite(fout);
          assign(sumfile,'TELO2SUM.'+filext);   {$I-} append(sumfile); {$I+} if (ioresult>0) then rewrite(sumfile);
          write(fout,crlf,'TELO2 ' + itoa(maxx)+'*'+itoa(maxx) + ' ' +DateTimeToStr(date+time) + ' ' + ToText(aging)+' '); if (not discriminating) then write(fout,'NOT_'); writeln(fout,'DISCRIMINATING');
          writeln(fout,'Init count=',initcount,'; Food added=',foodadded:5:3,
                  '; Full telo=',fulltelo,'; Rep thresh=',repthresh:5:3,'; Init horniness=',ihorniness:5:3,'; diffusion=',diffusion:6:4,'; mortality=',mort:6:4,
                  '; mutation=',ftoa(mutation,5),'; conjcost=',conjcost:5:3,'; portion=',portion:5:3);
          if (upcase(foutname[length(foutname)])='V') then writeln(fout,CSVheader) else writeln(fout,headerstr);
          writeln(headerstr);
          close(fout);
          end;

procedure Init;
          var i            :integer;
              x,y,g,j      :word;
          begin
          {$ifndef NDEBUG} randomize; {$endif NDEBUG}
          t:=0; birthcount:=0; conjcount:=0;
          gnorg:=initcount; outcome:=0.5;
          for y:=1 to maxx do for x:=1 to maxx do with c[y,x] do begin
            norg:=0;
            food:=random*foodadded;
            end;
          for i:=1 to gnorg do with o[i] do begin
            energy:=repthresh*half*(1+random-random);
            telomere:=round(fulltelo*half*(1+random-random));
            x:=succ(random(maxx)); y:=succ(random(maxx));
            horniness:=ihorniness*(1+random-random);
horniness:=1;
            immunity:=random(twotothe[nC]);
            case aging of ALL : thegene:=TRUE;
                         NONE : thegene:=FALSE;
                MUTABLE,MIXED : thegene:= (random(2)=0);
                     SEPARATE : thegene:= (2*x>maxx);
                     end; {case}
            with c[y,x] do begin
              inc(norg);
              orglist[norg]:=i;
              end; {with c[y,x]}
            end; {for i}
          foutname:='Telome2m.'+filext;
          end; {Init}

(* No longer needed - just equal bytes
function Match(a,b :immgenes):boolean;
         var g :byte;
         begin
         result:=false;
         for g:=1 to nC do if (a[g] xor b[g]) then exit;
         result:=true;
         end;
*)
function SiteDiversity(y,x :word):double;
         var count     :array[0..maxgene] of integer;
             i,sqsum   :integer;
             dnorg     :double;
         begin with c[y,x] do begin
         if (norg=0) then begin result:=half*maxgenep; exit; end;
         for i:=0 to maxgene do count[i]:=0;
         for i:=1 to norg do
           inc(count[o[orglist[i]].immunity]);
         sqsum:=0;
         for i:=0 to maxgene do sqsum:=sqsum+sqr(count[i]);
         dnorg:=norg;
         result:=sqr(dnorg)/sqsum;
         end;end;

function AvgSiteDiversity:double;
         var y,x :word;
         begin
         result:=0;
         for y:=1 to maxx do for x:=1 to maxx do
           result:=result+SiteDiversity(y,x);
         result:=result/gridsiz;
         end;

procedure ComputeStats;
          var i,genesum,bestimmunity,worstimmunity,vulnerablesitecount  :integer;
              immunecount :array[1..nC] of integer;
              indanger :array[1..nC] of boolean;
              norg2sum    :comp;
              maxnorg,second,third,
              g,y,x       :word;
              clumpiness,
              birth2sexratio,
              avgtelo,avgfood          :double;

   function Homogeneous:boolean;
            var i        :word;
                template :immgenes;
            begin
            result:=false;
            template:=o[c[y,x].orglist[1]].immunity;
            for i:=2 to c[y,x].norg do if (o[c[y,x].orglist[1]].immunity<>template) then exit;
            result:=false;
            end;

          begin {ComputeStats}
          {$ifdef NDEBUG} IntegrityCheck; {$endif}
          avgfood:=0;  avgtelo:=0;  avghorn:=0; norg2sum:=0; maxnorg:=0; second:=0; third:=0; genesum:=0; vulnerablesitecount:=0;
          for g:=1 to nC do immunecount[g]:=0;
          for y:=1 to maxx do for x:=1 to maxx do with c[y,x] do begin
            avgfood:=avgfood+food;
            norg2sum:=norg2sum+sqr(norg);
            if (third<norg) then
              if (norg>=maxnorg)then begin third:=second; second:=maxnorg; maxnorg:=norg; end
              else if (norg>=second) then begin third:=second; second:=norg; end
              else third:=norg;
            for g:=1 to nC do indanger[g]:=true;
            if (norg=0) or (Homogeneous) then inc(vulnerablesitecount);
            end;
          bestimmunity:=immunecount[1]; worstimmunity:=immunecount[1];
          for g:=2 to nC do begin
            if (immunecount[g]>bestimmunity) then bestimmunity:=immunecount[g];
            if (immunecount[g]<worstimmunity) then worstimmunity:=immunecount[g];
            end;
          avgfood:=avgfood/gridsiz;
          clumpiness:=norg2sum/gnorg; clumpiness:=log(clumpiness/gnorg);
          for i:=1 to gnorg do begin
            if (o[i].thegene) then begin inc(genesum); avgtelo:=avgtelo+o[i].telomere; end;
            avghorn:=avghorn+o[i].horniness;
            end;
          avgtelo:=avgtelo/gnorg;
          if (conjcount>0) then birth2sexratio:=birthcount/conjcount else birth2sexratio:=1000;
          avghorn:=avghorn/gnorg;
          outcome:=genesum/gnorg;
          writeln(t:7,gnorg:7,avgfood:7:1,avgtelo:6:0,100*avghorn:8:2,birth2sexratio:8:1,100*genesum/gnorg:7:2,'%',clumpiness:6:2,maxnorg:5,100*vulnerablesitecount/gridsiz:7:1,'%',',',AvgSiteDiversity:6:2);
          {append(fout); writeln(fout,t,',',gnorg,',',avgtelo:8:0,',',avghorn:8:3,',',birth2sexratio:7:1,',',100*genesum/gnorg:7:2,'%',clumpiness:6:2,',',maxnorg,',',vulnerablesitecount,',',round(bestimmunity/gridsiz),'%,',round(worstimmunity/gridsiz),'%');
          close(fout);}
          birthcount:=0; conjcount:=0;
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

procedure Mitosis(i :integer);
          const safetymargin=round(maxorg*0.99);  saveyy:word=0; savexx:word=0;
          var yy,xx,g :word;
          begin
          overflow:=true;
          if (gnorg>safetymargin) then begin
            if (t<500) then exit;
            writeln('gnorg=',gnorg); append(fout); writeln(fout,'gnorg=',gnorg); close(fout); exit;
            end;
          inc(birthcount);
          with o[i] do begin
            energy:=half*energy;
            if (thegene) then dec(telomere);
            if (random<inviscosity) then RandomVNNeighbor(y,x,yy,xx) else begin yy:=y; xx:=x; end;
            end;
          inc(gnorg);
          o[gnorg]:=o[i];
          with o[gnorg] do begin
            x:=xx; y:=yy; Mutate(horniness);
            if (random<mutprob) then thegene:=not thegene;
            {for g:=1 to nC do if (random<mutprob) then immunity:=immunity xor twotothe[g];}
            end;
          with c[yy,xx] do
             if (norg=maxcap) then begin
               if (saveyy<>yy) or (savexx<>xx) then writeln('Overflow at site (',yy,',',xx,')');
               dec(gnorg); overflow:=true; saveyy:=yy; savexx:=xx;
               end
             else begin inc(norg); orglist[norg]:=gnorg; end;
          end;
(*
procedure Conjugate(i,j :integer);
          var swap :double;
              rg,rgc,newi,newj   :byte;
          begin
          if (discriminating) then
             if (o[i].thegene) xor (o[j].thegene) then exit;
          inc(conjcount);
          with o[i] do energy:=energy-repthresh*conjcost;
          with o[j] do energy:=energy-repthresh*conjcost;
          if (random(2)=0) then begin swap:=o[i].horniness; o[i].horniness:=o[j].horniness; o[j].horniness:=swap; end;
          rg:=random(maxgenep);
          rgc:=maxgene-rg; {complement, with 1s where rg has zeros and vice versa}
          newi:=(o[i].immunity and rg) + (o[j].immunity and rgc);
          newj:=(o[j].immunity and rg) + (o[i].immunity and rgc);
          o[i].immunity:=newi; o[j].immunity:=newj;
          o[i].telomere:=round(fulltelo); o[j].telomere:=round(fulltelo);
          end;
*)

procedure Conjugate(i,j :integer); {This version works only for nC=2}
          var swap :double;
              dif,rg,rgc,newi,newj   :byte;
          begin
          if (discriminating) then
             if (o[i].thegene) xor (o[j].thegene) then exit;
          inc(conjcount);
          with o[i] do energy:=energy-repthresh*conjcost;
          with o[j] do energy:=energy-repthresh*conjcost;
          if (random(2)=0) then begin swap:=o[i].horniness; o[i].horniness:=o[j].horniness; o[j].horniness:=swap; end;
          if (o[i].immunity xor o[j].immunity = 3) then {This is the only case for which swapping makes a difference}
            if (random(2)=0) then begin
              o[i].immunity:=1;
              o[j].immunity:=2;
              end
            else begin
              o[i].immunity:=3;
              o[j].immunity:=0;
              end;
          o[i].telomere:=round(fulltelo); o[j].telomere:=round(fulltelo);
          end;

procedure DiffuseAndAddFood;
          var y,x :word;
              newfood :array[1..maxx,1..maxx] of double;
          begin
          for y:=1 to maxx do for x:=1 to maxx do
            newfood[y,x]:=(foodretention-diffusion)*c[y,x].food + diffusion*quarter*(c[prev(y),x].food+c[next(y),x].food+c[y,prev(x)].food+c[y,next(x)].food);
          for y:=1 to maxx do for x:=1 to maxx do begin
            c[y,x].food:=newfood[y,x]+foodadded;
            if (c[y,x].food>10*foodadded) then c[y,x].food:=10*foodadded;
            end;
          end;

procedure Die(i :integer);  {this is a little complicated because of the double bookkeeping.  Not only do we remove o[i] from the global list, we also have to find the
                             site he was in and delete i from the site's orglist.  Then, after we promote o[norg] to compact the list, we have to find the site where
                             o[norg] was in the orglist, and tell the site that o[norg] is now to be called by the name o[i].}
          var j :word;
          begin
          with c[o[i].y,o[i].x] do begin
            j:=0; repeat inc(j) until (j>norg) or (orglist[j]=i);
            if (j>norg) then begin write('A norg=',norg,';  Bookkeeping error: org[',i,'] not found in site [',o[i].y,',',o[i].x,']...'); readln; end;
            orglist[j]:=orglist[norg]; dec(norg);
            end;
          if (i=gnorg) then begin dec(gnorg); exit; end; {otherwise, compact the list}
          o[i]:=o[gnorg];
          with c[o[i].y,o[i].x] do begin
            j:=0; repeat inc(j) until (j>norg) or (orglist[j]=gnorg);
            if (j>norg) then begin write('B norg=',norg,';  Bookkeeping error: org[',i,'] not found in site [',o[i].y,',',o[i].x,']...'); readln; end;
            orglist[j]:=i;
            end;
          dec(gnorg);
          end;

procedure Cat(y,x :word; template :byte);
          var i,yy,xx  :word;
          begin
          i:=1; while (i<=c[y,x].norg) do
            if (template=o[c[y,x].orglist[i]].immunity) then
            Die(c[y,x].orglist[i]) else inc(i);
{$ifdef CONTAGION}
          if (c[y,x].norg=0) then begin
            i:=0;
            repeat
              inc(i); RandomVNNeighbor(y,x,yy,xx);
            until (i=5) or (c[yy,xx].norg>0);
            if (c[yy,xx].norg>0) then Cat(yy,xx);
            end;
{$endif CONTAGION}
          end;

procedure Catastrophe;
          var y,x      :word;
              template :byte;
          begin
          template:=random(maxgenep);
          for y:=1 to maxx do for x:=1 to maxx do
            if (random<catfreq) then Cat(y,x,template);
          end;

{$ifdef MEANSITE}
procedure ConjugationOpp; {Probability of conjugation is unlinked from site size}
          var y,x :word;
              i,j,k :integer;
              avgsite :double;
          begin
          avgsite:=gnorg/gridsiz;
          for y:=1 to maxx do for x:=1 to maxx do with c[y,x] do
            for k:= 1 to round(sqr(avgsite)) do begin
               i:=succ(random(norg)); j:=succ(random(norg));
               if (random<o[orglist[i]].horniness*o[orglist[j]].horniness) and (i<>j) then Conjugate(orglist[i],orglist[j]);
               end;
          end;
{$else MEANSITE}
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
{$endif MEANSITE}
(*
procedure Eat;
          var i :integer;
          begin {use shuffled list, because order matters}
          for i:=1 to gnorg do
            with o[s[i]] do with c[y,x] do begin
you can't do this - have to have the food eaten limited by energy already accumulated, not just by available food. Otherwise you get unreasonable growth
You have to go back and include this in the original Telomere model as well.
            energy:=energy - col*repthresh + food*portion;
            food:=food-portion;
            if (food<0) then food:=0;
            end;
          end;
*)
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
              if (energy>RepThresh) then Mitosis(i);
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
          Catastrophe;
          {$ifdef NDEBUG} IntegrityCheck; {$endif}
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
          if (t mod 100=0) then ComputeStats
          end;

procedure OneRun;
          begin
          Init;
          IntegrityCheck;
          OpenOutputFile;
          ComputeStats;
          repeat OnePeriod until (gnorg<5) or (t>=stoptime) or (outcome<0.07) or (outcome>0.93);
          append(sumfile);
          write(sumfile,crlf,'TELOMERE ' + itoa(maxx)+'*'+itoa(maxx) + DateTimeToStr(date+time) + ' ' + ToText(aging)); if (not discriminating) then write(sumfile,' NOT'); writeln(sumfile,' DISCRIMINATING');
          writeln(sumfile,'Init count=',initcount,'; Food added=',foodadded:5:3,
                  '; Full telo=',fulltelo,'; Init rep thresh=',repthresh:5:3,'; Init horniness=',ihorniness:5:3,'; diffusion=',diffusion:6:4,'; mortality=',mort:6:4,
                  '; mutation=',ftoa(mutation,5),'; conjcost=',conjcost:5:3,'; portion=',portion:5:3);
          write(sumfile,'Outcome=',outcome:6:3,'  t=',t:6,'   ');
          close(sumfile);
          append(csvfile);
          if (outcome>half) then write(csvfile,1000/t:6:3) else write(csvfile,-1000/t:6:3);
          writeln(csvfile,',',totext(aging),',',discriminating,',',mort:5:3,',',conjcost:5:3,',',t:6,',',outcome:6:3);
          close(csvfile);
          end;



{Main}

begin
Init;
IntegrityCheck;
OpenOutputFile;
ComputeStats;
repeat OnePeriod until (gnorg<5) or (t>=stoptime) {or (outcome<0.01) or (outcome>0.99)};
write('DONE...'); readln;
end.





repeat
OpenSummaryFile;
z:=0;
for i:=1 downto 0 do for j:=true downto false do for k:=0 to 2 do for l:=0 to 2 do for m:=0 to 2 do begin
  aging:=ad[i]; discriminating:=j; mort:=mm[k]; splitmult:=ss[l]; conjcost:=cc[m];
  inc(z);
  if (z>0) then OneRun;
  end;
until false;  
end.
