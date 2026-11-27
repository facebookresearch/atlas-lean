# Range report of a valid kd-tree

Let $t$ be a kd-tree over $\mathbb{Z}^d$ that
satisfies the kd invariant, and let $lo, hi, p \in \mathbb{Z}^d$. Then $p$ occurs in the range
report of $t$ for the box $[lo, hi]$ if and only if $p$ is one of the points stored in $t$ and
$lo_i \le p_i \le hi_i$ for every coordinate $i$.
