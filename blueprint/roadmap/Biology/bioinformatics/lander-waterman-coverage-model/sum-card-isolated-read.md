# Exact count of isolated reads

Let $G$, $N$ and $W$ be natural numbers with $2W + 1 \le G$. The number of pairs of a position
$p \in \{0, \dots, G-1\}$ and a start tuple $(s_1, \dots, s_N) \in \{0, \dots, G-1\}^N$ such that
$p$ holds an [isolated read](isolated-read.md) for the window $W$ is

$$G\, N\, \bigl(G - (2W + 1)\bigr)^{N - 1},$$

that is, summed over the positions $p$, the number of start tuples with an isolated read at $p$.
Here $N - 1$ is natural subtraction; for $N = 0$ the factor $N$ makes both sides $0$.
