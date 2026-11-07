# Bad-character table of Boyer–Moore preprocessing

Let $p = p_0 \cdots p_{m-1}$ be a
pattern over the alphabet $\{0, \dots, \sigma - 1\}$ and let $B$ be the bad-character table
computed by the Boyer–Moore preprocessing of $p$. For every symbol $c$, either $B_c = m$ and
$p_k \ne c$ for every $k$ with $k + 1 < m$, or there is $j$ with $j + 1 < m$ and $p_j = c$ such
that $B_c = m - 1 - j$ and every $k$ with $k + 1 < m$ and $p_k = c$ satisfies $k \le j$.

Thus $B_c$ is the distance from the last position of $p$ to the rightmost occurrence of $c$
before that position, or $m$ if $c$ does not occur there.
