# Universal rates trichotomy for countable label spaces

Let $X$ be a Polish space, $Y$ a countable label space, and $H \subseteq Y^X$ a measurable class (in the sense of Bousquet, Hanneke, Moran, van Handel and Yehudayoff) that is **nondegenerate**: some $h_1, h_2 \in H$ and $x, x' \in X$ have $h_1(x) = h_2(x)$ and $h_1(x') \ne h_2(x')$. In the realizable universal model with the 0-1 loss:

- if $H$ has no infinite multiclass Littlestone tree, $H$ is learnable with optimal rate $e^{-n}$;
- if $H$ has an infinite multiclass Littlestone tree but no infinite DSL tree, $H$ is learnable at rate $\log^2 n / n$ and not learnable faster than $1/n$;
- if $H$ has an infinite DSL tree, $H$ requires arbitrarily slow rates.

For a finite label set $Y = [k]$ (and $|H| > k + 2$) the middle rate is exactly $1/n$, and the three conditions can equivalently be stated with Natarajan–Littlestone trees, since then an infinite NL tree, an infinite DSL tree and an infinite GL tree exist together. For infinite $Y$ this fails: there are countable $X, Y$ and $H \subseteq Y^X$ with an infinite DSL tree but no NL tree of depth $2$.

## Proof sketch

The exponential case reruns the Gale–Stewart argument with multiclass online learners. For the linear case, the winning learner strategy in the DSL game yields after finitely many steps a data-dependent restriction of the target to a class of finite DS dimension, and the multiclass PAC learner for finite DS dimension then gives a near-linear rate. The arbitrarily slow lower bound places mass on the tuples of an infinite DSL tree; since every vector of a pseudo-cube has a neighbour in every direction, the unseen coordinate's label is ambiguous given the sample, which plays the role of the fair coin in the binary proof.

## Depends on

- [Realizable distributions, learning curves and universal rates](universal-rate.md)
- [Pseudo-cube trees for multiclass universal rates](dsl-tree.md)
- [Infinite Littlestone trees](infinite-littlestone-tree.md)

## Proof depends on

- [Combinatorial characterization of the three universal rates](universal-rate-characterization.md)
- [DS dimension characterizes multiclass PAC learnability](../../../ds-dimension-characterizes-multiclass-pac-learnability.md)

## Sources

- S. Hanneke, S. Moran, Q. Zhang, "Universal Rates for Multiclass Learning", COLT (2023), arXiv:2307.02066, Definitions 2, 3, 5 and 7, Theorems 4, 8, 9 and 10, Corollary 11.
- A. Kalavasis, G. Velegkas, A. Karbasi, "Multiclass Learnability Beyond the PAC Framework: Universal Rates and Partial Concept Classes", NeurIPS (2022), arXiv:2210.02297, Theorems 1 and 2.
