# Boyer–Moore preprocessing

Given a pattern $p = p_0 \cdots p_{m-1}$ over the alphabet
$\{0, \dots, \sigma - 1\}$, this computes a bad-character table $B$ of length $\sigma$ and a
strong good-suffix table $G$ of length $m$. The table $B$ starts with every entry equal to $m$,
and then for $k = 0, 1, \dots, m - 2$ in turn the entry $B_{p_k}$ is set to $m - 1 - k$. For
$G$, let $s_i$ be the length of the longest common suffix of $p_0 \cdots p_i$ and $p$, computed
with the Z algorithm on the reversed pattern. The table $G$ starts with every entry equal to
$m$; then for $i = m - 1, \dots, 0$ in turn, if $s_i = i + 1$, every entry $G_j$ with
$j < m - 1 - i$ that still equals $m$ is set to $m - 1 - i$; finally, for
$i = 0, 1, \dots, m - 2$ in turn, the entry $G_{m - 1 - s_i}$ is set to $m - 1 - i$.

The event cost includes table slots, copies, fill iterations and canonical Z events;
it does not count machine instructions or unbounded-integer bit operations.
