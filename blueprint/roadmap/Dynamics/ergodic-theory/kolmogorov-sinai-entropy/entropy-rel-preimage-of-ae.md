# Relative entropy of a pulled-back partition under an a.e. factor map

Let $(X, \mu)$ and $(Y, \nu)$ be probability spaces, $T : X \to X$ a quasi-measure-preserving map ($T$ is
measurable and $\mu(T^{-1} A) = 0$ whenever $\mu(A) = 0$), $S : Y \to Y$ a measurable map, and
$\pi : X \to Y$ a measure-preserving map with $\pi \circ T = S \circ \pi$ $\mu$-almost everywhere. Then for every
family $\eta = (D_i)_{i \in I}$ of measurable subsets of $Y$ indexed by a finite set $I$,

$$h_\mu(T, \pi^{-1}\eta) = h_\nu(S, \eta),$$

where $\pi^{-1}\eta = (\pi^{-1} D_i)_{i \in I}$ and $h$ is the [entropy relative to a partition](entropy-rel.md).
The atoms of the two [dynamical refinements](iterate-join.md)
[agree up to null sets](iterate-join-preimage-ae-eq.md) with preimages of atoms, which have the same measure.
