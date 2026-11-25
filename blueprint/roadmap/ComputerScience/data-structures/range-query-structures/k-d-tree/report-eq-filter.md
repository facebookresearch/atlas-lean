# Correctness of the kd-tree range report

For every valid kd-tree $t$ over
$\mathbb{Z}^d$ and all $lo, hi \in \mathbb{Z}^d$, the range report of $t$ for the box
$[lo, hi]$ equals the list of points of $t$, in left-to-right order, that lie in the box,
that is, the points $p$ with $lo_i \le p_i \le hi_i$ for every coordinate $i$.
