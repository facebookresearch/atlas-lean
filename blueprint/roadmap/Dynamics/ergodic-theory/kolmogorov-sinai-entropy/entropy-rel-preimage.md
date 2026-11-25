# Relative entropy of a pulled-back partition

Let $(X, \mu)$ and $(Y, \nu)$ be probability spaces, $T : X \to X$ a map, $S : Y \to Y$ a measurable map, and
$\pi : X \to Y$ a measure-preserving map with $\pi \circ T = S \circ \pi$. Then for every family
$\eta = (D_i)_{i \in I}$ of measurable subsets of $Y$ indexed by a finite set $I$,

$$h_\mu(T, \pi^{-1}\eta) = h_\nu(S, \eta),$$

where $\pi^{-1}\eta = (\pi^{-1} D_i)_{i \in I}$ and $h$ is the [entropy relative to a partition](entropy-rel.md):
by [pullback along the factor map](iterate-join-preimage.md), the two [dynamical refinements](iterate-join.md)
have atoms of equal measure.
