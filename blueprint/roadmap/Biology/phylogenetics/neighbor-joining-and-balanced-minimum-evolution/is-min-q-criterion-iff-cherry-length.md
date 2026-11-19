# Q-minimality is cherry-length minimality at a run state

Let $d$ be a symmetric dissimilarity on a finite set $X$ with $d(x, x) = 0$, and let a [run of neighbor joining](../neighbor-joining/njrun.md) on $d$ reach the cluster set $S$, with $|S| \ge 3$, and cluster dissimilarity $D$. Then for distinct $a, b \in S$: $Q(a, b) \le Q(a', b')$ for all distinct $a', b' \in S$ if and only if $L_{ab} \le L_{a'b'}$ for all distinct $a', b' \in S$, where $Q$ is the [Q-criterion](../neighbor-joining/q-criterion.md) and $L$ the [cherry-tree length](cherry-length.md), both for $D$ on $S$.
