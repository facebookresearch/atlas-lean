# Accumulator range report of a valid kd-tree

Let $t$ be a valid kd-tree over
$\mathbb{Z}^d$, let $lo, hi \in \mathbb{Z}^d$, and let $acc$ be a list of points. The
accumulator range report of $t$ for the box $[lo, hi]$ onto $acc$ equals the list of points
of $t$, in left-to-right order, that lie in the box (the points $p$ with
$lo_i \le p_i \le hi_i$ for every coordinate $i$), followed by $acc$.
