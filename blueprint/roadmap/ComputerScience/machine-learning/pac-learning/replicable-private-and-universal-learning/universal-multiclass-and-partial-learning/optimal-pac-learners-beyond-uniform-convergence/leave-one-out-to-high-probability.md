# Leave-one-out bounds give optimal high-probability risk bounds for aggregated learners

Let $A$ be a permutation-invariant learner such that, for some $M \ge 1$, $\mathrm{LOO}_A(S) \le M/(n+1)$ holds for every realizable sample $S$ of size $n+1$ (worst case over samples). Then a simple aggregation of $A$ (a majority vote over $A$ run on a constant number of disjoint parts of the sample) satisfies, for every realizable $D$ and every $\delta \in (0,1)$,

$$
\mathrm{er}_D(\hat h) \le C\, \frac{M + \log(1/\delta)}{n}
$$

with probability at least $1-\delta$, for an absolute constant $C$. Applied to the one-inclusion-graph predictor of a binary class of VC dimension $d$ this gives the optimal bound $O((d + \log(1/\delta))/n)$ without uniform convergence; applied to multiclass classes it gives an optimal bound in terms of the one-inclusion hypergraph density; and it determines the optimal sample complexity of partial concept classes.

## Proof sketch

The worst-case leave-one-out bound controls not only the mean of the risk but the probability that the risk exceeds $t$: if the risk were large with probability $\delta$, then on fresh test points the leave-one-out count would exceed $M$ on a large set of samples, contradicting the worst-case bound via a symmetrization and a binomial tail estimate. A majority vote over three or a constant number of independent runs converts the resulting weak-tail bound into the exponential tail $\log(1/\delta)/n$.

## Depends on

- [Permutation-invariant learners and leave-one-out error](permutation-invariant-learner-leave-one-out.md)
- [One-inclusion hypergraphs, orientations and out-degree](../list-learning-and-multiclass-pseudo-cubes/one-inclusion-hypergraph.md)
- [The realizable distribution family](../../../occam-bound-for-consistent-learners/realizable-family.md)

## Proof depends on

- [Optimal sample complexity of realizable PAC learning](../../../optimal-sample-complexity-of-realizable-pac-learning.md)

## Sources

- I. Aden-Ali, Y. Cherapanamjeri, A. Shetty, N. Zhivotovskiy, "Optimal PAC Bounds without Uniform Convergence", FOCS (2023), arXiv:2304.09167.
