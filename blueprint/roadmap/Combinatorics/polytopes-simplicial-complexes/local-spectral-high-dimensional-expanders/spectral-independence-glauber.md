# Spectral independence implies polynomial mixing of Glauber dynamics

Let $\mu$ be a distribution on $\{0,1\}^n$ (equivalently on subsets of $[n]$) that is $(\eta_0, \dots, \eta_{n-2})$-spectrally independent: for each $0 \le i \le n-2$, every conditional distribution of $\mu$ obtained by pinning $i$ coordinates has pairwise influence matrix with maximum eigenvalue at most $\eta_i$. Then the Glauber dynamics (single-site heat-bath) for $\mu$ has spectral gap at least

$$
\frac{1}{n} \prod_{i=0}^{n-2} \Bigl( 1 - \frac{\eta_i}{n-i-1} \Bigr).
$$

A uniform bound $\eta_i \le \eta$ alone does not make this product large, and it need not even keep its last factors positive; the conclusion depends on the whole sequence $(\eta_i)$. For the hard-core model on a graph of maximum degree $\Delta \ge 3$ at fugacity $\lambda = (1-\delta)\lambda_c(\Delta)$, where $\lambda_c(\Delta) = (\Delta-1)^{\Delta-1}/(\Delta-2)^{\Delta}$ and $0 < \delta < 1$, one has $\eta_i \le \min\{C(\delta), \tfrac{\lambda}{1+\lambda}(n-i-1)\}$ with $C(\delta) \le \exp(O(1/\delta))$. The Glauber dynamics started from any independent set $\tau$ then has mixing time $O\bigl(((1+\lambda)n)^{1+C(\delta)} \log\frac{1}{\varepsilon\,\mu(\tau)}\bigr)$, and $Z_G(\lambda)$ has a fully polynomial randomized approximation scheme.

## Proof sketch

Glauber dynamics on $\mu$ is the down-up walk on the top faces of the weighted $n$-partite complex of $\mu$. Spectral independence of the pinned distributions makes the links of $i$-faces $\eta_i/(n-i-1)$-spectral expanders, and the Alev-Lau local-to-global bound turns these link bounds into the stated product. For the hard-core model, correlation decay on the self-avoiding walk tree below the uniqueness threshold bounds every pinned influence matrix by $C(\delta)$, while the trivial bound $\tfrac{\lambda}{1+\lambda}(n-i-1)$ keeps the last factors positive; together they bound the product below by a constant multiple of $((1+\lambda)n)^{-C(\delta)}$.

## Depends on

- [Spectral independence of a distribution on the hypercube](spectral-independence.md)

## Proof depends on

- [Alev–Lau local-to-global bound for the down-up walk](alev-lau-local-to-global.md)

## Sources

- N. Anari, K. Liu, S. Oveis Gharan, "Spectral independence in high-dimensional expanders and applications to the hardcore model", FOCS (2020), arXiv:2001.00303.
- V. L. Alev, L. C. Lau, "Improved analysis of higher order random walks and applications", STOC (2020), arXiv:2001.02827.
