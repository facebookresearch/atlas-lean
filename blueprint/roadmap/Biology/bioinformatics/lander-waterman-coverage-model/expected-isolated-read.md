# Expected number of isolated reads (exact)

Let $G$, $N$ and $W$ be natural numbers with $2W + 1 \le G$ (so $G \ge 1$). Summed over the
positions $p \in \{0, \dots, G-1\}$, the [normalized counts](normalized-count.md) of the start
tuples in which $p$ holds an [isolated read](isolated-read.md) for the window $W$ add up to

$$N \Bigl(1 - \frac{2W + 1}{G}\Bigr)^{N - 1},$$

where $N - 1$ is natural subtraction (for $N = 0$ the factor $N$ makes the value $0$). When the
$N$ start positions are independent and uniform on $\{0, \dots, G-1\}$, this is the expected
number of isolated reads; under the single-piece condition with $W = L - T$ it is the expected
number of apparent islands of exactly one clone.
