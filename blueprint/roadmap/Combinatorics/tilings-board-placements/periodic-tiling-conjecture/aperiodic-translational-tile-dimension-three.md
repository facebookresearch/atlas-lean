# An aperiodic translational tile in dimension three and lattice minimality

A finite $T\subset\mathbb Z^d$ tiles with complement $A\subset\mathbb Z^d$ when $T\times A\to\mathbb Z^d$, $(t,a)\mapsto t+a$, is a bijection. Such a complement is fully periodic if it is invariant under translations by a finite-index subgroup of $\mathbb Z^d$.

There is a nonempty finite $T\subset\mathbb Z^3$ that tiles, but every complement is not fully periodic. The *same* $T$ has thickening $\Omega=T+[0,1]^3\subset\mathbb R^3$ with an almost-everywhere tiling by real translates: for Lebesgue-almost every $x$ there is a unique $a\in A$ with $x-a\in\Omega$. No such Euclidean complement $A$ is invariant under all integer combinations of a real basis of $\mathbb R^3$. Moreover $3$ is the least natural number $d$ for which a nonempty finite lattice tile has no fully periodic lattice complement.

## Depends on

- [Discrete aperiodic tiling equation](is-aperiodic-tiling-equation.md)
- [Continuous aperiodic tiling equation](is-aperiodic-continuous-tiling-equation.md)

- Discrete bijective tilings, almost-everywhere Euclidean tilings, and the two full-periodicity predicates.

## Proof depends on

- Three-dimensional aperiodic construction; real-translation obstruction after thickening; existence of periodic complements in every lattice dimension below three.

## Expansion

Identify finite-index invariance with the finite coset union in the existing discrete predicate; in the Euclidean predicate, use local finiteness of a bounded positive-volume tile complement to compare a lattice-invariant complement with the finite coset formulation. Wire the discrete witness to the Euclidean thickening without restricting its translation centers to integers. Split the lower-dimensional periodicity proof from the dimension-three construction and handle $d=0$ explicitly.

## Sources

- OpenAI Math, [`periodic_tiling_counterexample_and_minimality`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PeriodicTilingThree.lean#L52-L61) (statement and local definitions).
