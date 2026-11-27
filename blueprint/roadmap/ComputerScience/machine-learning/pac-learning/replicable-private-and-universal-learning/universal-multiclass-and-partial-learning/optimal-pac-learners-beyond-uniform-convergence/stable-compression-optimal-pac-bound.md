# Stable compression schemes are optimal PAC learners

If $H$ has a stable sample compression scheme of size $k$, then the learner $S \mapsto \rho(\kappa(S))$ satisfies, for every realizable distribution $D$, every sample size $n > 2k$ and every $\delta \in (0,1)$, with probability at least $1-\delta$,

$$
\mathrm{er}_D\big(\rho(\kappa(S))\big) < \frac{2}{n - 2k}\Big(k \ln 4 + \ln\frac{1}{\delta}\Big),
$$

with no $\log n$ factor, unlike the classical compression bound. Examples include the support vector machine for halfspaces, the closure algorithm for intersection-closed classes, and maximum classes (which gives proper sample complexity $\Theta((d + \log(1/\delta))/\varepsilon)$ for maximum classes of VC dimension $d$).

## Proof sketch

Stability gives a uniform leave-one-out bound: an example outside $\kappa(S \cup \{z\})$ is classified correctly because its removal does not change the output, so at most $k$ of $n+1$ points can be misclassified by the hold-one-out outputs. A direct argument exploiting that the output depends on the sample only through its compression set, which is unchanged by removing the other examples, upgrades this in-expectation bound to the stated exponential tail without aggregation.

## Depends on

- [Stable sample compression schemes](stable-sample-compression-scheme.md)
- [The realizable distribution family](../../../occam-bound-for-consistent-learners/realizable-family.md)

## Sources

- O. Bousquet, S. Hanneke, S. Moran, N. Zhivotovskiy, "Proper Learning, Helly Number, and an Optimal SVM Bound", COLT (2020), arXiv:2005.11818, Definition 14, Theorem 15, Corollary 16 and Appendix D.
