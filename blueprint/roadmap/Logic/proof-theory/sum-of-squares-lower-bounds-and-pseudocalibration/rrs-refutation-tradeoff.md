# Raghavendra–Rao–Schramm: SoS refutes random CSPs below the spectral threshold

Let $k \ge 2$ and let $P : \{\pm 1\}^k \to \{0, 1\}$ be a predicate with expected value $\mathbb{E}[P]$ under a uniformly random assignment. For every $\delta \in (0, 1]$ and every constant $\varepsilon > 0$, with high probability over a random instance $\Phi$ of $\mathrm{CSP}(P)$ on $n$ variables with clause density

$$
\frac{m}{n} \ge \widetilde{O}\bigl(n^{(k/2 - 1)(1 - \delta)}\bigr),
$$

the sum-of-squares hierarchy of degree $O(n^\delta)$ strongly refutes $\Phi$, certifying $\mathrm{opt}(\Phi) \le \mathbb{E}[P] + \varepsilon$; here $\widetilde O$ hides polylogarithmic factors and constants depending on $k$ and $\varepsilon$, and a spectral algorithm achieves the same guarantee. For random $k$-XOR the same holds for every $\delta \in [0, 1)$, certifying $\mathrm{opt}(\Phi) \le 1/2 + \varepsilon$, via the largest eigenvalue of a matrix of dimension $2^{\widetilde O(n^\delta)}$. With degree $D = n^\delta$, the density condition reads $m \ge \widetilde O\bigl(n^{k/2}/D^{k/2-1}\bigr)$; for predicates that support a $(k-1)$-wise uniform distribution, this trade-off between number of constraints and degree matches the Kothari–Mori–O'Donnell–Witmer lower bound up to logarithmic factors.

## Proof sketch

Reduce strong refutation to bounding the injective norm of the random $k$-tensor built from the constraints (via the Fourier expansion of $P$). Lift to a $D$-th tensor power with $D = n^\delta$ and bound the spectral norm of a symmetrized Kikuchi-type matrix of dimension $\binom{n}{D}$, whose entries are sums of independent random signs, by the matrix Chernoff inequality; the resulting bound is a degree-$O(D)$ SoS certificate. General predicates reduce to XOR instances on subsets of the variables through the Fourier expansion of $P$, following Allen, O'Donnell and Witmer.

## Depends on

- [Refutation of random constraint satisfaction problems](random-csp-refutation.md)
- [The Lasserre / sum-of-squares hierarchy for Boolean polynomial optimization](lasserre-hierarchy.md)

## Sources

- P. Raghavendra, S. Rao, T. Schramm, "Strongly refuting random CSPs below the spectral threshold", STOC (2017), arXiv:1605.00058, Theorems 1.3 and 1.5 and Section 5.
- S. R. Allen, R. O'Donnell, D. Witmer, "How to refute a random CSP", FOCS (2015), arXiv:1505.04383.
