# Upper bound on the splay-tree potential

A binary tree with $n$ nodes has [potential](potential.md) at most $n \log_2 n$ (which is $0$ for
$n = 0$): each of its $n$ subtrees has at most $n$ nodes. Together with the [nonnegativity of the
potential](potential-nonneg.md), it bounds the net potential drop over any sequence of splays by
$n \log_2 n$.

## Sources

- D. D. Sleator and R. E. Tarjan, *Self-adjusting binary search trees*, J. ACM 32(3) (1985)
  652–686, §2, the remark before Theorem 1 (net decrease in potential at most
  $\sum_i \log_2(W/w(i))$, which is $n \log_2 n$ for unit weights).
