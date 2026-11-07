# Recurrence for the number of $L^*$-block sums

**Recurrence for the number of $L^*$-block sums.** Let $L = (e_1, \dots, e_N)$ be a list of
natural numbers with $N \ge 2$ and $e_1 \ne 0$, index coefficient functions from $1$, and let
$C_n$ be the number of functions $\mathbb N \to \mathbb N$ that are sums of disjoint proper
$L^*$-blocks with support intervals inside $[1, n]$. Then $C_k = \sum_{j=1}^{k} e_j C_{k-j}$ for
$1 \le k \le N$, and $C_n = \sum_{k=1}^{N-1} e_k C_{n-k} + (1 + e_N) C_{n-N}$ for $n \ge N + 1$.

## Sources

- Sungkon Chang, *Distribution of Zeckendorf Expressions*, INTEGERS 25 (2025), Article A25, Proposition 4 (arXiv:2308.12872v1, Section 4.1).
