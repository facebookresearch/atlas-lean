# Reversal of the block of positions i to j of a list

For a list of integers $\pi = (\pi_0, \dots, \pi_{m-1})$, with positions counted from $0$, and
natural numbers $i$ and $j$, the reversal $\operatorname{rev}_{i,j}(\pi)$ is the list formed by
the first $i$ entries of $\pi$, then the next $j + 1 - i$ entries in reverse order, then the
entries from position $j + 1$ on. On the intended domain $i \le j < m$ this reverses the block
of positions $i$ to $j$: the result is $\pi_0, \dots, \pi_{i-1}$, then
$\pi_j, \pi_{j-1}, \dots, \pi_i$, then $\pi_{j+1}, \dots, \pi_{m-1}$.

Outside that domain the definition still returns a list. The block length $j + 1 - i$ is a
truncated difference, $0$ when $j < i$: the result is then the first $i$ entries of $\pi$ (all
of $\pi$ if $i \ge m$) followed by the entries from position $j + 1$ on, which is $\pi$ itself
for $i = j + 1$ but repeats the entries in positions $j + 1$ to $\min(i, m) - 1$ when
$j + 1 < \min(i, m)$. When $i \le j$ and $j \ge m$, the block runs to the end of the list, so
the entries from position $i$ on are reversed.
