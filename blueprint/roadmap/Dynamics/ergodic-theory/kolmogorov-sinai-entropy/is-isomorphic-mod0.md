# Isomorphism modulo null sets

Two dynamical systems $(X, \mu, T)$ and $(Y, \nu, S)$ are *isomorphic modulo null sets* if there are
measure-preserving maps $\pi : X \to Y$ and $\rho : Y \to X$ such that

- $\rho \circ \pi = \mathrm{id}$ $\mu$-almost everywhere and $\pi \circ \rho = \mathrm{id}$ $\nu$-almost everywhere;
- $\pi \circ T = S \circ \pi$ $\mu$-almost everywhere and $\rho \circ S = T \circ \rho$ $\nu$-almost everywhere.

This is measure-theoretic isomorphism, written with maps defined almost everywhere. Sarig's definition asks for
invariant sets of full measure $X' \subset X$, $Y' \subset Y$ and a measure-preserving bijection
$X' \to Y'$ with measurable inverse intertwining $T$ and $S$; on nonempty spaces such a bijection, extended by a
constant off $X'$ (and its inverse off $Y'$), gives maps $\pi$ and $\rho$ as above. Unlike an everywhere
conjugacy, the notion ignores null sets such as the fixed points of a Bernoulli shift, which is why
[Kolmogorov's non-isomorphism](not-isomorphic-bernoulli-uniform-three-t.md) and
[Ornstein's theorem](ornstein-isomorphism.md) are stated with it.
[Kolmogorov–Sinai entropy is invariant under it](ks-entropy-eq-of-is-isomorphic-mod0.md), and
[an everywhere conjugacy by a measure-preserving equivalence is a special case](is-isomorphic-mod0-of-measurable-equiv.md).

## Sources

- O. Sarig, *Lecture Notes on Ergodic Theory* (2023), Definition 1.3.
