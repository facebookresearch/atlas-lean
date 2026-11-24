# Set with the least cost per new element

Given a list $F$ of finite sets, a finite set $U$
and a rational cost $w(S)$ for each finite set $S$, this is the first set $S$ in $F$ with
$S \cap U \ne \emptyset$ that minimizes the ratio $w(S) / |S \cap U|$ among the sets of $F$ meeting
$U$, or nothing when no set of $F$ meets $U$.
