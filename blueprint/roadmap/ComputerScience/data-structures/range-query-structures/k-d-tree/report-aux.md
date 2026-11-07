# Accumulator range report of a kd-tree

Points are vectors in $\mathbb{Z}^d$ with
coordinates $p_0, \dots, p_{d-1}$; the box $[lo, hi]$ consists of the points $p$ with
$lo_i \le p_i \le hi_i$ for every $i$. For a kd-tree $t$ and a list $acc$ of points, the
accumulator report of $t$ for $[lo, hi]$ onto $acc$ is defined by recursion on $t$. For the
empty tree it is $acc$. For a leaf $p$ it is $p$ followed by $acc$ if $p$ lies in the box,
and $acc$ otherwise. For a split node with axis $a$, split value $s$, left child $L$ and
right child $R$, let $acc'$ be $acc$ if $hi_a < s$ and the report of $R$ onto $acc$
otherwise; the result is $acc'$ if $s < lo_a$ and the report of $L$ onto $acc'$ otherwise.

The accumulator avoids repeatedly appending the results of left subtrees, so building the
output list costs work linear in the number of reported points; the traversal still visits
every node that pruning does not cut, which can be the whole tree even for an empty report.
No complexity bound is formalized.
