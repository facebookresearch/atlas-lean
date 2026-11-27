# Membership in the range report of a built kd-tree

Let $d \ge 1$, let
$a \in \{0, \dots, d-1\}$, let $P$ be a list of points in $\mathbb{Z}^d$ and let
$lo, hi, p \in \mathbb{Z}^d$. Then $p$ occurs in the range report, for the box $[lo, hi]$, of the
kd-tree built from $P$ by median splits starting at axis $a$ if and only if $p$ occurs in $P$ and
$lo_i \le p_i \le hi_i$ for every coordinate $i$.
