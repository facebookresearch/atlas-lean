# Rademacher complexity

The empirical Rademacher complexity of a set $A \subseteq \mathbb{R}^n$ of value vectors,
$R(A) = \frac1n \mathbb{E}_\sigma \sup_{a \in A} \sum_i \sigma_i a_i$, averaged over the $2^n$
sign vectors, in the convention of Shalev-Shwartz and Ben-David (Section 26.1, equation (26.5)); Bartlett and
Mendelson's convention $\mathbb{E} \sup_a \lvert \frac2n \sum_i \sigma_i a_i \rvert$ differs by
the absolute value and the factor $2$. Its structural calculus (monotonicity, convex hulls,
scaling, sums, translations and Lipschitz contraction), Massart's finite-class lemma and the
resulting bound $\sqrt{2 d \log(e n / d) / n}$ for classes of VC dimension $d$ follow below, with the
risk bound that turns it into a generalization guarantee.

- [Empirical Rademacher complexity](rademacher-complexity.md)
- [Monotonicity](rademacher-complexity-mono.md)
- [Convex hull invariance](rademacher-complexity-convex-hull.md)
- [Scaling](rademacher-complexity-smul.md)
- [Minkowski sums](rademacher-complexity-add.md)
- [A single vector has complexity zero](rademacher-complexity-singleton.md)
- [Translation invariance](rademacher-complexity-add-singleton.md)
- [The contraction lemma](rademacher-complexity-coord-map-le.md)
- [Massart's finite-class lemma](rademacher-complexity-le-of-finite.md)
- [Rademacher complexity of a VC class](rademacher-complexity-sign-patterns-le.md)
- [Partial binomial sums are at most $(eD/r)^r$](../../../../Combinatorics/binomial-coefficients/binomial-sums/bounds-on-partial-sums-of-binomial-coefficients/sum-choose-le-exp-mul-div-pow.md) (in Combinatorics)
- [Rademacher complexity of a VC class, explicit rate](rademacher-complexity-sign-patterns-le-v.md)
- [The Rademacher risk bound](risk-le-empirical-add-rademacher.md)

## Supporting definitions and lemmas

- [Correlation with a sign vector](sign-corr.md)
- [Supremum of the correlations](sup-corr.md)
- [Reversing every sign](flip-signs.md)
- [Reversing every sign negates the correlation](sign-corr-flip-signs.md)
- [Sign averages are invariant under reversing every sign](sum-flip-signs.md)
- [Correlations average to zero](sum-sign-corr.md)
- [Correlations on a bounded set are bounded above](bdd-above-sign-corr-image.md)
- [Supremum over the convex hull](sup-corr-convex-hull.md)
- [Exponential moment as a product of hyperbolic cosines](sum-exp-sign-corr.md)
- [Exponential moment of a Rademacher sum](average-exp-sign-corr-le.md)
- [Optimizing $a/\lambda + \lambda b$](le-two-mul-sqrt-of-forall.md)
- [Coordinatewise map](coord-map.md)
- [Reversing one sign](flip-at.md)
- [Splitting off one coordinate of the correlation](sign-corr-coord-map-update.md)
- [Coordinatewise Lipschitz maps preserve boundedness](is-bounded-coord-map-image.md)
- [One step of the contraction argument](sum-sup-corr-le-update.md)
- [Sign pattern of a subset](sign-vector.md)
- [Sign patterns of a set family](sign-patterns.md)
- [The VC dimension is at most the size of the ground set](../../../../Combinatorics/extremal-set-theory/vc-dim-le-card.md) (in Combinatorics)
- [Cost vectors on a sample](cost-vectors.md)
- [The margin cost vectors](margin-costs.md)
- [The margin costs of voting classifiers are no more complex than the base classifiers](rademacher-complexity-margin-costs-conve.md)
- [The ramp cost](ramp.md)
- [The ramp dominates the zero-one loss](indicator-le-ramp.md)
- [The ramp is dominated by the margin error](ramp-le-indicator.md)
- [The ramp $\rho_\theta$ is $1/\theta$-Lipschitz](lipschitz-with-ramp.md)
- [The complexity term of the margin bound for voting classifiers](rademacher-complexity-ramp-costs-convex.md)

## Related topics

- [Concentration of the uniform deviation](../bounded-differences-uniform-deviation.md): the bounded-differences half of the risk bound.
- [Rademacher type and cotype](../../../../Analysis/banach-spaces/geometry-of-banach-spaces/rademacher-type-and-cotype/README.md): the same uniform averages over sign vectors, in Banach-space geometry.
- [Hedge algorithm](../../online-learning-and-boosting/hedge-algorithm/README.md): the online counterpart, where regret replaces generalization error.
- [Two-layer neural networks and Barron space](../../supervised-learning/two-layer-neural-networks-and-barron-space/README.md): homogeneity, contraction and Massart's lemma combine into the bound $2 Q \sqrt{2 \log(2d) / n}$ for path-norm balls of two-layer ReLU networks, independent of the width.
- [AdaBoost](../../online-learning-and-boosting/adaboost/README.md): voting classifiers whose training margins AdaBoost drives up; the margin-cost bounds here are the complexity side of the margins explanation.
