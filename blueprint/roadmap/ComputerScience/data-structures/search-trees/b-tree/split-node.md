# Splitting a B-tree node

Let $t$ be a minimum degree, $s = t - 1$ (so $s = 0$ when
$t = 0$), $k_1, \dots, k_m$ a list of keys and $c_1, \dots, c_n$ a list of B-trees. If
$m > s$, splitting returns the pair of internal nodes formed by the keys $k_1, \dots, k_s$
with the first $t$ children (all of them if $n < t$) and by the keys $k_{s+2}, \dots, k_m$
with the children after the first $t$, together with the key $k_{s+1}$ promoted between
them. If $m \le s$, it returns the single internal node with keys $k_1, \dots, k_m$ and
children $c_1, \dots, c_n$ unchanged.

On an overfull node with $2t$ keys and $t \ge 1$, the promoted key $k_t$ is the median key.
