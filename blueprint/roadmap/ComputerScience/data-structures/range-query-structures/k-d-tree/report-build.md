# Range report of a built kd-tree as a filter

Let $d \ge 1$. For every starting axis
$a$, every list $P$ of points of $\mathbb{Z}^d$ and all $lo, hi \in \mathbb{Z}^d$, let $T$ be
the kd-tree built from $P$ starting at axis $a$. The range report of $T$ for the box
$[lo, hi]$ equals the list of points of $T$, in left-to-right order, that lie in the box,
that is, the points $p$ with $lo_i \le p_i \le hi_i$ for every coordinate $i$.
