# Range report of a kd-tree built from the first axis

Let $d \ge 1$, let $P$ be a list
of points in $\mathbb{Z}^d$ and let $lo, hi, p \in \mathbb{Z}^d$. Then $p$ occurs in the range
report, for the box $[lo, hi]$, of the kd-tree built from $P$ by median splits starting at
axis $0$ if and only if $p$ occurs in $P$ and $lo_i \le p_i \le hi_i$ for every coordinate
$i$.
