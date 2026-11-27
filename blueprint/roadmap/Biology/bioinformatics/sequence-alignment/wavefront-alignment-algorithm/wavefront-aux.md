# Fuelled wavefront recurrence

For [linear gap penalties](linear-penalties.md) $\chi$ (mismatch) and $g$ (gap) and sequences $x, y$, define $W_n(s, k)$, an integer offset or "unreachable", for natural numbers $n, s$ and integer diagonals $k$:

- $W_0(s, k)$ is unreachable;
- $W_{n+1}(0, k)$ is the [slide](slide.md) of $0$ along diagonal $0$ if $k = 0$, and unreachable otherwise;
- for $s \ge 1$, $W_{n+1}(s, k)$ is unreachable if $k < -|x|$ or $k > |y|$;
- otherwise, for $s \ge 1$, let $c$ be the largest of the reachable candidates $W_n(s - \chi, k) + 1$ (if $\chi \le s$), $W_n(s - g, k - 1) + 1$ and $W_n(s - g, k + 1)$ (both if $g \le s$); $W_{n+1}(s, k)$ is the slide along $k$ of $\min(c, m_k)$, with $m_k$ the [largest valid offset](max-offset.md), and unreachable if there is no reachable candidate.
