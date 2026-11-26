# Node balance of a walk's traversal counts

Let $V$ and $E$ be finite sets and let each arc $e \in E$ run from its tail $t(e) \in V$ to its head $h(e) \in V$; parallel arcs and loops are allowed. Let $B$ be the signed incidence matrix of the network, $B_{ve} = [h(e) = v] - [t(e) = v]$, where $[P]$ is $1$ if $P$ holds and $0$ otherwise. A list of arcs is a walk from $o$ to $d$ if it is empty only when $o = d$, its first arc leaves $o$, the head of each arc is the tail of the next, and its last arc enters $d$. If $l$ is a walk from $o$ to $d$ and $c(e)$ is the number of occurrences of the arc $e$ in $l$, then for every $v \in V$

$$(Bc)_v = [d = v] - [o = v].$$

In particular a closed walk, with $o = d$, has zero balance at every vertex.
