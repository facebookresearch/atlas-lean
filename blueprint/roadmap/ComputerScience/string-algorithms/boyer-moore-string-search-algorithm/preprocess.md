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

The cost charged is $\sigma$ for creating $B$; when $m \ge 1$ it adds one unit per update of $B$,
$m$ for reversing the pattern, the cost of the Z algorithm on the reversed pattern (one unit per
outer step and per letter comparison), $m$ for reversing its output, $m$ for initialising $G$, one
unit per step $i$ of the first loop on $G$ and per position $j$ visited while filling, and one unit
per update of the second loop. When $m = 0$ the cost is $\sigma$ and $G$ is empty.
