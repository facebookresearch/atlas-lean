# Semi-balanced edge list

A list $E$ of ordered pairs of vertices is semi-balanced for
vertices $v$ and $t$ when, for every vertex $x$, the number of pairs in $E$ with first component
$x$ plus $[x = t]$ equals the number with second component $x$ plus $[x = v]$, where $[P]$ is $1$
if $P$ holds and $0$ otherwise. So for $v \ne t$, $v$ has one more outgoing than incoming
occurrence, $t$ one more incoming than outgoing, and every other vertex is balanced; for $v = t$
every vertex is balanced.
