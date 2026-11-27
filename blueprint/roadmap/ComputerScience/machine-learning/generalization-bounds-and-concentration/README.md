# Generalization bounds and concentration

Uniform deviation bounds between the empirical and the expected risk, obtained from concentration inequalities, and their use for empirical risk minimization: if every deviation is at most $s$, the empirical risk minimizer is within $2 s$ of the best predictor of the class. For a finite class, Hoeffding's inequality and a union bound give a deviation of order $\sqrt{\log |F| / n}$; for a general class, McDiarmid's bounded-differences inequality concentrates the supremum of the deviations around its mean, and Rademacher averages control that mean, dimension free for balls of linear predictors. The two pages marked as expositions describe published results; each names what it relies on, and how, under Informally uses. Algorithmic stability gives a complementary route that involves no complexity of the class: if replacing one example changes the loss of the learned predictor by at most $\varepsilon$ (uniform stability), the expected generalization gap is at most $\varepsilon$ (Hardt, Recht and Singer 2016, Theorem 2.2, after Bousquet and Elisseeff 2002), and stochastic gradient descent on convex, smooth, Lipschitz losses is uniformly stable (their Theorem 3.8). The Rademacher complexity topic covers the structural calculus of the empirical Rademacher complexity, Massart's finite-class lemma, the bound for classes of finite VC dimension through the Sauer–Shelah lemma, the contraction lemma and the Rademacher risk bound.

In the [PAC-Bayes bounds](pac-bayes-bounds/README.md), Catoni's bound for bounded losses holds with high probability simultaneously for every posterior, through the Donsker–Varadhan change of measure.

- [Expected risk](risk.md)
- [Empirical risk](empirical-risk.md)
- [Learning a discrete distribution in total variation](learning-a-discrete-distribution-in-total-variat/README.md)
- [Measurability of the empirical risk](measurable-empirical-risk.md)
- [Empirical risk minimization under a uniform deviation bound](risk-le-add-two-mul-of-forall-abs-sub-le.md)
- [Rademacher averages of a finite class](rademacher-finite-class.md)
- [Uniform deviation of the empirical risk over a finite class](measure-real-exists-abs-empirical-risk-s.md)
- [Uniform deviation over a finite class, high-probability form](one-sub-le-measure-real-forall-abs-empir.md)
- [Uniform deviation for a finite class](finite-class-uniform-deviation.md) (exposition)
- [Concentration of the uniform deviation](bounded-differences-uniform-deviation.md) (exposition)
- [Rademacher average of a ball of linear predictors](rademacher-average-linear-ball-le.md)
- [Rademacher complexity](rademacher-complexity/README.md)
- [PAC-Bayes bounds](pac-bayes-bounds/README.md)
- [Algorithmic stability](algorithmic-stability/README.md)

- [Generalization bound for sample compression schemes](generalization-bound-for-sample-compression-schemes.md)
- [Generalization bound for norm-bounded linear predictors with Lipschitz loss](generalization-bound-for-norm-bounded-linear-predictors-with.md)
- [Stability of regularized loss minimization](stability-of-regularized-loss-minimization.md)
- [Shattering lower bound for PAC learning](shattering-lower-bound-for-pac-learning.md)
- [Learning a discrete distribution in total variation](remaining-clauses-of-learning-a-discrete-distribution-in-tot.md)
- [Weak learnability implies PAC learnability via boosting](weak-learnability-implies-pac-learnability-via-boosting.md)
- [VC and Natarajan classes: uniform convergence and the fundamental theorems](vc-and-natarajan-classes/README.md)
- [Limits of uniform convergence for explaining deep-learning generalization](limits-of-uniform-convergence-for-explaining-deep-learning-g.md)

## Related topics

- [Hedge algorithm](../online-learning-and-boosting/hedge-algorithm/README.md): regret bounds, the online counterpart of uniform deviation bounds; the $\sqrt{T \log n}$ regret of Hedge mirrors the $\sqrt{\log \lvert \mathcal{F} \rvert / n}$ deviation of a finite class.
- [Effective ranks and benign overfitting](../supervised-learning/effective-ranks-and-benign-overfitting/README.md): the excess risk of the minimum-norm interpolating estimator is analysed through the spectrum of the covariance rather than through a uniform deviation bound over the class.
- [Hoeffding's inequality](../../../Probability/concentration-inequalities/hoeffding-s-inequality/README.md): the per-predictor concentration step.
- [McDiarmid's inequality](../../../Probability/concentration-inequalities/mcdiarmid-s-inequality/README.md): concentration of the supremum of the deviations.
- [Rademacher type and cotype](../../../Analysis/banach-spaces/geometry-of-banach-spaces/rademacher-type-and-cotype/README.md): Rademacher averages in Hilbert spaces, behind the bound for linear predictors.
- [Positive-definite kernels](../../../Analysis/hilbert-spaces/positive-definite-kernels/README.md): feature maps of kernels, whose balls are balls of linear predictors.
- [Gradient descent](../../../Analysis/convex-analysis-and-variations/gradient-descent/README.md): the subgradient method and stochastic gradient descent, whose $1/\sqrt{t}$ rate matches the $1/\sqrt{n}$ estimation error.
- [Sub-exponential variables and Bernstein's inequality](../../../Probability/concentration-inequalities/sub-exponential-variables-and-bernstein-s-inequa/README.md)
- [Uniform laws and Rademacher complexity](../../../Probability/high-dimensional-probability/uniform-laws-and-rademacher-complexity/README.md)
- [Matrix concentration inequalities](../../../Probability/concentration-inequalities/matrix-concentration-inequalities/README.md)
- [Differential privacy](../../cryptography/differential-privacy/README.md): concentration for a fixed query does not suffice when the queries themselves are generated adaptively from the data, outside any fixed class covered by a union bound; if the choice is differentially private, the empirical mean of the chosen query still concentrates (Dwork, Feldman, Hardt, Pitassi, Reingold and Roth 2015, the transfer theorem).
- [PAC learning](../pac-learning/README.md): the realizable case, where a consistent learner over a finite class needs only $\log(|H|/\delta)/\varepsilon$ examples and no concentration inequality.
- [Two-layer neural networks and Barron space](../supervised-learning/two-layer-neural-networks-and-barron-space/README.md): Rademacher bounds for path-norm balls of two-layer networks and the a priori estimate of the population risk of the path-norm regularized estimator.
- [Finite-sample expressivity of ReLU networks](../supervised-learning/finite-sample-expressivity-of-relu-networks/README.md): two-layer ReLU networks with $2n + d$ weights fit every labelling of $n$ distinct points, so uniform deviation bounds over such a class cannot explain generalization at that sample size.

## Research directions

- [Generalization of trained finite-width neural networks with feature learning](generalization-of-trained-finite-width-networks.md)
- [Sharp guarantees for out-of-distribution generalization](out-of-distribution-generalization-guarantees.md)
