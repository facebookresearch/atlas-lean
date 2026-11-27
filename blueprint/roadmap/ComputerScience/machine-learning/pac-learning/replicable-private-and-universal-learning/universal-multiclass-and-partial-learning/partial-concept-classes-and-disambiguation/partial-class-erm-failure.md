# Empirical risk minimization fails for partial concept classes

There is a partial concept class $H$ with $\mathrm{VC}(H) = 1$ such that for every total class $\bar H \subseteq \{0,1\}^X$ some empirical risk minimizer for $\bar H$ is not a PAC learner for $H$. Moreover, there is a partial class $H$ with $\mathrm{VC}(H) = 1$ such that every learning algorithm that outputs only total concepts has an image (the set of all hypotheses it ever outputs) of infinite VC dimension.

## Proof sketch

The class is built from the disambiguation lower bound: if some total class of finite VC dimension made ERM succeed, its hypotheses would induce a disambiguation of finite VC dimension, contradicting the existence of partial VC-one classes that cannot be disambiguated. The image statement follows similarly, since the image of a successful learner restricted to realizable samples must contain consistent total extensions of all sufficiently large realizable samples.

## Depends on

- [Partial concept classes and their VC and Littlestone dimensions](partial-concept-class.md)

## Proof depends on

- [VC dimension characterizes PAC learnability of partial concept classes](partial-class-pac-characterization.md)
- [A partial class of VC dimension one with no finite-VC disambiguation](vc-one-partial-class-without-disambiguation.md)
- [Uniform convergence implies ERM is an agnostic PAC learner](../../../agnostic-pac-learning-and-uniform-convergence/uniform-convergence-implies-erm-is-an-agnostic-pac-learner.md)

## Sources

- N. Alon, S. Hanneke, R. Holzman, S. Moran, "A Theory of PAC Learnability of Partial Concept Classes", FOCS (2021), arXiv:2107.08444.
