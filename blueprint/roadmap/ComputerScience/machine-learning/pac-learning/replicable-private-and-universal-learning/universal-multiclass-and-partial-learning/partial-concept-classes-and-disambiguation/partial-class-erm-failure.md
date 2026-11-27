# Empirical risk minimization fails for partial concept classes

There is a partial concept class $H$ with $\mathrm{VC}(H) = 1$ such that for every total class $\bar H \subseteq \{0,1\}^X$ some empirical risk minimizer for $\bar H$ is not a PAC learner for $H$. Moreover, there is a partial class $H$ with $\mathrm{VC}(H) = 1$ such that every learning algorithm that outputs only total concepts has an image (the set of all hypotheses it ever outputs) of infinite VC dimension.

## Proof sketch

Take the partial class of VC dimension one all of whose disambiguations have infinite VC dimension. If a total class $\bar H$ does not disambiguate $H$, some finite sample realizable by $H$ is not realizable by $\bar H$, and an ERM for $\bar H$ errs on a distribution uniform over that sample. If $\bar H$ disambiguates $H$, then $\mathrm{VC}(\bar H) = \infty$, and the shattering lower bound gives, for each sample size, a realizable distribution on which a suitable ERM for $\bar H$ (choosing among consistent hypotheses adversarially) fails. For the image statement, the image of a learner that PAC learns $H$ with total outputs must be rich enough to fit, up to small error, every realizable sample, which forces infinite VC dimension by the same disambiguation lower bound.

## Depends on

- [Partial concept classes and their VC and Littlestone dimensions](partial-concept-class.md)

## Proof depends on

- [A partial class of VC dimension one with no finite-VC disambiguation](vc-one-partial-class-without-disambiguation.md)
- [Shattering lower bound for PAC learning](../../../../generalization-bounds-and-concentration/shattering-lower-bound-for-pac-learning.md)

## Sources

- N. Alon, S. Hanneke, R. Holzman, S. Moran, "A Theory of PAC Learnability of Partial Concept Classes", FOCS (2021), arXiv:2107.08444, Theorems 5 and 6.
