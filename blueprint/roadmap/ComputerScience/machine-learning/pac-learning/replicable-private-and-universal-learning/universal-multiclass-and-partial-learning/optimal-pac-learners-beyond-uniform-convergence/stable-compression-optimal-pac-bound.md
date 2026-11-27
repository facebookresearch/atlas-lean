# Stable compression schemes are optimal PAC learners

If $H$ has a stable sample compression scheme of size $k$, then the learner $S \mapsto \rho(\kappa(S))$ satisfies, for every realizable distribution $D$, every $n$ and every $\delta \in (0,1)$, with probability at least $1-\delta$,

$$
\mathrm{er}_D\big(\rho(\kappa(S))\big) \le C\,\frac{k + \log(1/\delta)}{n}
$$

for an absolute constant $C$, without the $\log n$ factor of the classical compression bound. Examples include the support vector machine (size $n+1$ in $\mathbb{R}^n$ with offset), the closure algorithm for intersection-closed classes, and maximum classes.

## Proof sketch

Stability gives a uniform leave-one-out bound: an example outside $\kappa(S \cup \{z\})$ is classified correctly because its removal does not change the output, so at most $k$ of $n+1$ points can be misclassified by the hold-one-out outputs. The leave-one-out-to-high-probability conversion for permutation-invariant learners, adapted to stable schemes, upgrades this to the stated exponential tail without aggregation.

## Depends on

- [Stable sample compression schemes](stable-sample-compression-scheme.md)
- [The realizable distribution family](../../../occam-bound-for-consistent-learners/realizable-family.md)

## Proof depends on

- [Leave-one-out bounds give optimal high-probability risk bounds for aggregated learners](leave-one-out-to-high-probability.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, N. Zhivotovskiy, "Proper Learning, Helly Number, and an Optimal SVM Bound", COLT (2020), arXiv:2005.11818.
- I. Aden-Ali, Y. Cherapanamjeri, A. Shetty, N. Zhivotovskiy, "Optimal PAC Bounds without Uniform Convergence", FOCS (2023), arXiv:2304.09167.
