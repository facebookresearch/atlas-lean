# Threshold for a spanning comb (Comb Conjecture)

The statement that there are real numbers $0 < c \le C$ such that, with $n = k^2$ and the binomial random graph $G(n, p_c(n))$ on $\{0, \dots, n-1\}$, each pair being an edge independently with probability $p_c(n)$, the probability that $G(n, p_c(n))$ contains a copy of the comb on $k^2$ vertices tends to $0$ as $k \to \infty$, while for $G(n, p_C(n))$ it tends to $1$. Here $p_c(n)$ is $c \log n / n$ clamped to $[0, 1]$ and the comb is the graph on $\{0, \dots, k-1\}^2$ with spine edges $(i, 0)(i+1, 0)$ and tooth edges $(i, j)(i, j+1)$; copies need not be induced. Stated here as a proposition; its resolution: [The spanning comb has threshold of order log n / n](comb-threshold-log-over-n-holds.md).

In this formula $\log 0 = 0$ and division by zero gives $0$, so $p_c(0) = 0$; this does not affect the limits.

## Sources

- E. Lubetzky (with J. Kahn and N. Wormald), in Combinatorics, Oberwolfach Reports 11 (2014), no. 1, pp. 42–43, DOI 10.4171/OWR/2014/01.
