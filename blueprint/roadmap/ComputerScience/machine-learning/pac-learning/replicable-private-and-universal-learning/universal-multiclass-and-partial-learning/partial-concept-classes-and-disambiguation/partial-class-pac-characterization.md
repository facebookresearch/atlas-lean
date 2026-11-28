# VC dimension characterizes PAC learnability of partial concept classes

For every partial concept class $H \subseteq \{0,1,\star\}^X$ the following are equivalent:

- $\mathrm{VC}(H) < \infty$;
- $H$ is PAC learnable in the realizable setting;
- $H$ is agnostically PAC learnable.

When $\mathrm{VC}(H) = d$ and the distribution $P$ is $H$-realizable, majority votes of one-inclusion-graph predictors trained on prefixes of a sample $S \sim P^n$ have classification error at most $9.64\big(d/n + \log(2/\delta)/n\big)$ with probability at least $1-\delta$, so $H$ is learnable in the realizable setting from $O\big((d + \log(1/\delta))/\varepsilon\big)$ examples. These ordinary-error bounds need realizability: on a single point with an independent fair label every classifier errs with probability $1/2$. In the agnostic setting the guarantee is instead on the excess risk $\mathrm{er}_P(\hat h) - \inf_{h \in H} \mathrm{er}_P(h)$. The realizable bound is an upper bound for each class, optimal only in the worst case: for every $d \ge 1$ some class of VC dimension $d$ needs $\Omega\big((d + \log(1/\delta))/\varepsilon\big)$ examples for $\varepsilon, \delta$ below absolute constants, while a particular class can need far fewer (the two constants on one point need a single example).

## Proof sketch

Necessity follows from the usual shattering lower bound applied to a shattered set. For sufficiency, uniform convergence and ERM are unavailable, so one uses the one-inclusion graph predictor on the projection of $H$ to the sample plus the test point; the partial class projected to $n+1$ points has a one-inclusion graph orientation with out-degree at most $d$, which gives expected error $d/(n+1)$, and confidence boosting gives a high-probability bound, though not the optimal one; aggregating the predictors trained on prefixes and converting their leave-one-out bound into a high-probability bound gives the optimal upper bound. The agnostic case reduces to the realizable case by sample compression of size $\tilde O(d \log n)$.

## Depends on

- [Partial concept classes and their VC and Littlestone dimensions](partial-concept-class.md)
- [Learners and agnostic PAC learnability](../../../agnostic-pac-learning-and-uniform-convergence/learners-and-agnostic-pac-learnability.md)

## Proof depends on

- [Shattering lower bound for PAC learning](../../../../generalization-bounds-and-concentration/shattering-lower-bound-for-pac-learning.md)
- [Haussler-Littlestone-Warmuth expected error bound for the one-inclusion predictor](../../../sample-complexity-and-combinatorial-dimensions/packing-and-one-inclusion-graphs/one-inclusion-predictor-error-bound.md)
- [Leave-one-out bounds give optimal high-probability risk bounds for aggregated learners](../optimal-pac-learners-beyond-uniform-convergence/leave-one-out-to-high-probability.md)

## Sources

- N. Alon, S. Hanneke, R. Holzman, S. Moran, "A Theory of PAC Learnability of Partial Concept Classes", FOCS (2021), arXiv:2107.08444, Definition 2 and Theorem 3.
- I. Aden-Ali, Y. Cherapanamjeri, A. Shetty, N. Zhivotovskiy, "Optimal PAC Bounds without Uniform Convergence", FOCS (2023), arXiv:2304.09167, Corollary 2.10.
