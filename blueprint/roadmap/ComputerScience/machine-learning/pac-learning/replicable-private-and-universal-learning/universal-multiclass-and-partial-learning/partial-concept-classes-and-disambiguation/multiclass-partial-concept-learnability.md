# Multiclass partial concept classes with boundedly many labels

Let $Y$ be finite and let $H \subseteq (Y \cup \{\star\})^X$ be a multiclass partial concept class. Then $H$ is PAC learnable in the realizable setting if and only if its Natarajan dimension (defined using realizable label patterns) is finite, and the optimal universal rate of $H$ is exponential, linear or arbitrarily slow according to whether $H$ has no infinite multiclass Littlestone tree, has one but no infinite Natarajan–Littlestone tree, or has an infinite Natarajan–Littlestone tree.

## Proof sketch

With finitely many labels, Natarajan dimension controls the one-inclusion graph out-degree of projections by a factor logarithmic in $|Y|$, and the out-degree argument for partial binary classes carries over. For the universal rates, the Gale–Stewart games of the binary theory are run with multiclass branchings; finiteness of $Y$ makes Natarajan–Littlestone trees equivalent to pseudo-cube trees.

## Depends on

- [Partial concept classes and their VC and Littlestone dimensions](partial-concept-class.md)
- [N-shattering](../../../../../not-yet-classified/natarajan/nshatters.md)
- [Realizable distributions, learning curves and universal rates](../universal-learning-curves-and-littlestone-trees/universal-rate.md)
- [Pseudo-cube trees for multiclass universal rates](../universal-learning-curves-and-littlestone-trees/dsl-tree.md)

## Proof depends on

- [VC dimension characterizes PAC learnability of partial concept classes](partial-class-pac-characterization.md)
- [Universal rates trichotomy for countable label spaces](../universal-learning-curves-and-littlestone-trees/multiclass-universal-trichotomy.md)

## Sources

- A. Kalavasis, G. Velegkas, A. Karbasi, "Multiclass Learnability Beyond the PAC Framework: Universal Rates and Partial Concept Classes", NeurIPS (2022), arXiv:2210.02297.
