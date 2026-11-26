# Spanning trees of bounded degree have threshold of order log n / n

For every natural number $\Delta$ there are real numbers $0 < c \le C$ such that, for the binomial random graph $G(n, p)$ on $\{0, \dots, n-1\}$: the probability that $G(n, p_c(n))$ contains some tree on $\{0, \dots, n-1\}$ with all degrees at most $\Delta$ tends to $0$, and the probability that $G(n, p_C(n))$ contains every tree on $\{0, \dots, n-1\}$ with all degrees at most $\Delta$ tends to $1$, as $n \to \infty$. Here $p_c(n)$ is $c \log n / n$ (natural logarithm) clamped to $[0, 1]$, and copies need not be induced. That is, the proposition [Threshold for spanning trees of bounded degree (Kahn's conjecture)](bounded-degree-tree-threshold.md) holds.

In this formula $\log 0 = 0$ and division by zero gives $0$, so $p_c(0) = 0$; this does not affect the limits.

## Sources

- E. Lubetzky (with J. Kahn and N. Wormald), in Combinatorics, Oberwolfach Reports 11 (2014), no. 1, pp. 42–43, DOI 10.4171/OWR/2014/01.
- R. Montgomery, Spanning trees in random graphs, Adv. Math. 356 (2019), 106793, arXiv:1810.03299, https://arxiv.org/abs/1810.03299.
