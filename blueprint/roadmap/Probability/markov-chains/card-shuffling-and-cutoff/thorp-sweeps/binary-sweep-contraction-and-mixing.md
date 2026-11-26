# Binary coordinate-sweep contraction, sign, and fixed-sweep mixing

The positions are the Boolean $d$-cube. At coordinate $j$, independently and fairly swap or keep each pair of positions with the same other coordinates. A sweep applies one such layer at each $j$ in increasing order, with independent layer choices. Write $\mu_d$ for its law on permutations. There exist $g>0$ and $d_0$ such that for every $d\ge d_0$ and every unitary irreducible complex representation $\rho$ of dimension $D$,

$$
\left\|\sum_\pi\mu_d(\pi)\rho(\pi)\right\|_{\rm op}\le D^{-g}.
$$

For every $d>0$ the expected sign of a sweep is zero. There is one natural $w$ such that for every $\varepsilon>0$ and all sufficiently large $d$, from every deterministic initial permutation $\tau$ the law $\mu_d^{*w}(\cdot\,\tau^{-1})$ is within $\varepsilon$ in total variation of uniform. Convolution is the law of independent products, and the zeroth power is the identity mass. There is no assertion identifying a physical shuffle law.

**Conventions.** Use the permutation action on cube slots, the independent fair switch law and chronological product, and the finite-group Fourier operator and total variation.

## Depends on

- [Coordinate-fiber sweeps on the binary cube](binary-sweep-step-law.md)

## Proof depends on

Uniform representation-dependent contraction for the systematic sweep, sign cancellation, and $L^2$ Fourier summability sufficient for a single absolute number of sweeps.

## Expansion

Separate the sign cancellation via even/odd pairing from the operator estimate; handle the two one-dimensional representations distinctly in the mixing deduction. Quantify the exponent and the sweep count before the deck dimension and initial state.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BinarySweep.lean#L95-L101)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/238.md)
- [Accompanying manuscript: Conditional coordinate sweeps and analytic transfer](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Conditional-coordinate-sweeps-and-analytic-transfer-September-26-2026/main.pdf)
