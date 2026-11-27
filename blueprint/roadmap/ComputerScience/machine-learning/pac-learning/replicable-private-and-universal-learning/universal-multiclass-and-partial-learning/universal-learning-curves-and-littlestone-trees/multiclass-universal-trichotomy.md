# Universal rates trichotomy for countable label spaces

Let $Y$ be countable and $H \subseteq Y^X$ (with at least three concepts and the measurability assumptions of the source), learned under the 0-1 loss in the realizable universal model. Then, up to logarithmic factors in the linear case:

- $H$ is learnable at exponential rate if and only if it has no infinite multiclass Littlestone tree;
- otherwise $H$ is learnable at a near-linear rate $\tilde O(1/n)$ if and only if it has no infinite DSL tree;
- otherwise $H$ requires arbitrarily slow rates.

The constants in the bounds do not depend on the number of labels, and a class has an infinite GL tree if and only if it has an infinite NL tree.

## Proof sketch

The exponential case reruns the Gale–Stewart argument with multiclass online learners. For the linear case, the winning learner strategy in the DSL game yields after finitely many steps a data-dependent restriction of the target to a class of finite DS dimension, and the multiclass PAC learner for finite DS dimension then gives a near-linear rate. The arbitrarily slow lower bound places mass on the tuples of an infinite DSL tree; since every vector of a pseudo-cube has a neighbour in every direction, the unseen coordinate's label is ambiguous given the sample, which plays the role of the fair coin in the binary proof.

## Depends on

- [Realizable distributions, learning curves and universal rates](universal-rate.md)
- [Pseudo-cube trees for multiclass universal rates](dsl-tree.md)

## Proof depends on

- [Combinatorial characterization of the three universal rates](universal-rate-characterization.md)
- [DS dimension characterizes multiclass PAC learnability](../../../ds-dimension-characterizes-multiclass-pac-learnability.md)

## Sources

- S. Hanneke, S. Moran, Q. Zhang, "Universal Rates for Multiclass Learning", COLT (2023), arXiv:2307.02066.
- A. Kalavasis, G. Velegkas, A. Karbasi, "Multiclass Learnability Beyond the PAC Framework: Universal Rates and Partial Concept Classes", NeurIPS (2022), arXiv:2210.02297.
