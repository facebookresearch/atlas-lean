# Range report of a built kd-tree up to order

Let $d \ge 1$. For every starting axis $a$,
every list $P$ of points of $\mathbb{Z}^d$ and all $lo, hi \in \mathbb{Z}^d$, the range report
for the box $[lo, hi]$ of the kd-tree built from $P$ starting at axis $a$ is a permutation of
the list of entries of $P$ that lie in the box, that is, the points $p$ with
$lo_i \le p_i \le hi_i$ for every coordinate $i$.
