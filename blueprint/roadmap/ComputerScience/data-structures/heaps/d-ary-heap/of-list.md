# Building a $d$-ary min-heap from a list

Let $\alpha$ be a linearly ordered type, let
$r \in \mathbb{N}$ be a requested arity, and let $d = \max(2, r)$. The min-heap built from the
empty list is the empty min-heap of arity $d$, and the min-heap built from a list with head $x$
and tail $xs$ of elements of $\alpha$ is obtained by inserting $x$ into the min-heap built from
$xs$. Thus the min-heap built from $[x_1, \dots, x_n]$ starts from the empty min-heap of arity
$d$ and inserts $x_n$, then $x_{n-1}$, and so on, ending with $x_1$, each by $d$-ary
insertion.
