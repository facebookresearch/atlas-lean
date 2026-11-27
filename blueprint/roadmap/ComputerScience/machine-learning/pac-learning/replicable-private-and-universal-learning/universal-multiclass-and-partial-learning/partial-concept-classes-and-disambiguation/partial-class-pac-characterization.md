# VC dimension characterizes PAC learnability of partial concept classes

For every partial concept class $H \subseteq \{0,1,\star\}^X$ the following are equivalent:

- $\mathrm{VC}(H) < \infty$;
- $H$ is PAC learnable in the realizable setting;
- $H$ is agnostically PAC learnable.

When $\mathrm{VC}(H) = d$, the realizable sample complexity is $O\big((d + \log(1/\delta))/\varepsilon\big)$ up to a logarithmic factor in $1/\varepsilon$, and the optimal bound $\Theta\big((d + \log(1/\delta))/\varepsilon\big)$ is attained by aggregated one-inclusion-graph predictors.

## Proof sketch

Necessity follows from the usual shattering lower bound applied to a shattered set. For sufficiency, uniform convergence and ERM are unavailable, so one uses the one-inclusion graph predictor on the projection of $H$ to the sample plus the test point; the partial class projected to $n+1$ points has a one-inclusion graph orientation with out-degree at most $d$, which gives expected error $d/(n+1)$, and confidence boosting gives the high-probability bound. The agnostic case reduces to the realizable case by sample compression of size $\tilde O(d \log n)$.

## Depends on

- [Partial concept classes and their VC and Littlestone dimensions](partial-concept-class.md)
- [Learners and agnostic PAC learnability](../../../agnostic-pac-learning-and-uniform-convergence/learners-and-agnostic-pac-learnability.md)

## Proof depends on

- [Shattering lower bound for PAC learning](../../../../generalization-bounds-and-concentration/shattering-lower-bound-for-pac-learning.md)
- [Optimal sample complexity of realizable PAC learning](../../../optimal-sample-complexity-of-realizable-pac-learning.md)

## Sources

- N. Alon, S. Hanneke, R. Holzman, S. Moran, "A Theory of PAC Learnability of Partial Concept Classes", FOCS (2021), arXiv:2107.08444.
- I. Aden-Ali, Y. Cherapanamjeri, A. Shetty, N. Zhivotovskiy, "Optimal PAC Bounds without Uniform Convergence", FOCS (2023), arXiv:2304.09167.
