# Fundamental theorem of statistical learning (binary, 0-1 loss)

Let $H$ be a class of functions from $X$ to $\{0,1\}$ with 0-1 loss, satisfying the measurability conditions needed for
the uniform-convergence argument. The following are equivalent: (1) $H$ has the uniform convergence property;
(2) every ERM rule is an agnostic PAC learner for $H$; (3) $H$ is agnostic PAC learnable; (4) $H$ is PAC learnable;
(5) every ERM rule is a PAC learner for $H$; (6) $\mathrm{VCdim}(H) < \infty$.

## Expansion

This node states a precise result. A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: VC dimension of a class of binary functions.
- Statement prerequisite: empirical risk minimization rules.

## Depends on

- [Uniform convergence property and eps-representative samples](../../pac-learning/agnostic-pac-learning-and-uniform-convergence/uniform-convergence-property-and-eps-representative-samples.md)
- [Learners and agnostic PAC learnability](../../pac-learning/agnostic-pac-learning-and-uniform-convergence/learners-and-agnostic-pac-learnability.md)

## Proof depends on

- [VC classes have uniform convergence (upper half of the quantitative fundamental theorem)](vc-classes-have-uniform-convergence.md)
- [Shattering lower bound for PAC learning](../shattering-lower-bound-for-pac-learning.md)
- [Uniform convergence implies ERM is an agnostic PAC learner](../../pac-learning/agnostic-pac-learning-and-uniform-convergence/uniform-convergence-implies-erm-is-an-agnostic-pac-learner.md)

## Related topics

- [The fundamental theorem of PAC learning](../../pac-learning/is-paclearnable-realizable-family-iff-ha.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Theorem 6.7, proved in Section 6.5. <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
