# k-kick tree balls-to-slots scheme

Let $M$ be the number of slots and $1 \le k \le \log^* M - 1$. The *$k$-kick tree* fixes bin sizes $s_0 = M$ and, for $1 \le i \le k$, powers of two $s_i = \Theta((\log^{(i)} M)^6)$ dividing $M$; for each depth $i \in [0, k]$ the slots are partitioned into contiguous depth-$i$ bins of size $s_i$, each depth-$i$ bin ($i > 0$) lying inside one depth-$(i-1)$ bin, so the bins form a tree with one root bin of all slots. Each ball $x$ chooses a uniformly random leaf (depth-$k$ bin), giving its root-to-leaf path of bins $g_0(x), g_1(x), \dots, g_k(x)$, and an independent *depth cap* $s(x) \in [0, k]$ with $\Pr[s(x) < i] = 1/(\log^{(i)} M)^2$ for $1 \le i \le k$; its probe sequence runs through the slots of $g_k(x)$, then of $g_{k-1}(x)$, and so on up to $g_0(x)$. Every present ball has a depth $d$ and sits in a slot of $g_d(x)$. A depth-$i$ bin is *saturated* if it has no free slot and all its balls have depth at least $i$. To insert $x$, let $j$ be the largest index such that none of $g_0(x), \dots, g_j(x)$ is saturated, and give $x$ depth $i = \min(j, s(x))$. If $g_i(x)$ has a free slot, $x$ takes it; otherwise $x$ displaces a ball $x'$ of $g_i(x)$ of smaller depth $i' < i$, and $x'$ is placed in a free slot of $g_{i'}(x')$ or displaces a ball of still smaller depth there, and so on. A moved ball keeps its depth, so an insertion moves at most one ball at each depth below $i$ and has switching cost at most $k + 1$. Deletion only vacates the deleted ball's slot.

## Depends on

- [Balls-to-slots problem and probe complexity](balls-to-slots-problem.md)
- [Iterated logarithm and log-star](../dictionary-specifications/iterated-logarithm.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu, "On the Optimal Time/Space Tradeoff for Hash Tables", Proceedings of the 54th ACM Symposium on Theory of Computing (STOC), 2022; arXiv:2111.00602.
