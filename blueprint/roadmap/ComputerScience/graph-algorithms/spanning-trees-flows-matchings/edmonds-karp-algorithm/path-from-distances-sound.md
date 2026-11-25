# Soundness of distance-guided path reconstruction

Let $G$ be a directed adjacency graph on
a type $V$ whose Boolean test $\equiv$ on pairs of vertices holds exactly for equal vertices, let
$d$ be a partial labelling of the vertices by natural numbers, let $t$ and $u$ be vertices, and let
$k$ be a natural number. If the distance-guided reconstruction for $G$, $d$ and $t$ from $u$ with
$k$ steps left succeeds and returns a list $p$, then $p$ is a walk from $u$ to $t$ in $G$ (it is
nonempty, its first entry is $u$, its last entry is $t$, and every pair of consecutive entries is
an edge of $G$) and $p$ has exactly $k + 1$ entries.
