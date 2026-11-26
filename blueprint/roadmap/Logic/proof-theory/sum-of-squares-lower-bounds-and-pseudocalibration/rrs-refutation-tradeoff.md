# Raghavendra–Rao–Schramm: SoS refutes random CSPs below the spectral threshold

For every $k$-ary predicate $P$ and every $d \le n$, the degree-$d$ sum-of-squares relaxation strongly refutes, with high probability, random instances of $\mathrm{CSP}(P)$ with

$$
m \ge \widetilde{O}\Bigl(\frac{n^{k/2}}{d^{k/2 - 1}}\Bigr)
$$

constraints. For predicates that support a $(k-1)$-wise uniform distribution, this trade-off between number of constraints and degree matches the Kothari-Mori-O'Donnell-Witmer lower bound up to logarithmic factors.

## Proof sketch

Reduce strong refutation to bounding the injective norm of the random $k$-tensor built from the constraints (via the Fourier expansion of $P$). Lift to a $d$-th tensor power and bound the spectral norm of a symmetrized Kikuchi-type matrix of dimension $\binom{n}{d}$, whose entries are sums of independent random signs, by the matrix Chernoff inequality; the resulting bound is a degree-$d$ SoS certificate.

## Depends on

- [Refutation of random constraint satisfaction problems](random-csp-refutation.md)

## Proof depends on

- [Refutation of random constraint satisfaction problems](random-csp-refutation.md)

## Sources

- P. Raghavendra, S. Rao, T. Schramm, "Strongly refuting random CSPs below the spectral threshold", STOC (2017), arXiv:1605.00058.
- S. R. Allen, R. O'Donnell, D. Witmer, "How to refute a random CSP", FOCS (2015), arXiv:1505.04383.
