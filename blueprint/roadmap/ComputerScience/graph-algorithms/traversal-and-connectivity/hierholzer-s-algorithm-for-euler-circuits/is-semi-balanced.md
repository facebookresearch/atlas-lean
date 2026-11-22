# Semi-balanced directed multigraph

A finite directed multigraph is semi-balanced for
vertices $s$ and $t$ when, for every vertex $x$, the number of edge occurrences leaving $x$ plus
$[x = t]$ equals the number entering $x$ plus $[x = s]$, where $[P]$ is $1$ if $P$ holds and $0$
otherwise. So for $s \ne t$, one more edge occurrence leaves $s$ than enters it, one more enters
$t$ than leaves it, and every other vertex is balanced; for $s = t$ every vertex is balanced.
