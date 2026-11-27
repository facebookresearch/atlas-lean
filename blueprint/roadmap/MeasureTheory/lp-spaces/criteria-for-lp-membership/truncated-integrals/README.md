# L^p membership via truncated integrals

Let $0 < p < \infty$, let $S \subseteq \mathbb{R}$ be measurable, and let $f : \mathbb{R} \to F$ be
measurable, where $F$ is a second-countable normed additive commutative group with its Borel
$\sigma$-algebra. Then $f$ belongs to $L^p$ of Lebesgue measure restricted to $S$ if and only if
$\sup_{n \in \mathbb{N}} \int_{[-n, n] \cap S} \|f(x)\|^p \, dx < \infty$, the integrals being taken
in $[0, \infty]$.

## Idea

The integral of $\|f\|^p$ over $S$ is the increasing limit of the integrals over the truncations
$[-n, n] \cap S$, by the monotone convergence theorem, which the second statement records; so a
bound uniform in $n$ is the same as membership in $L^p$. Measurability cannot be dropped: a
non-measurable function can satisfy the bound.

## Statements

- [Characterization of $L^p$ membership via truncated integrals](mem-lp-iff-i-sup-lintegral-icc-inter-lt.md)
- [Lebesgue integrals over truncations of a set](lintegral-eq-i-sup-lintegral-icc-inter.md): used in the proof: integrals over $S$ as limits of integrals over its truncations.
