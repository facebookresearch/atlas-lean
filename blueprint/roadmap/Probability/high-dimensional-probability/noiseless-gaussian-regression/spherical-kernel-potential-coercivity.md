# Coercivity and convexity of a spherical kernel potential

Write $\sigma_d$ for the radial pushforward of uniform volume in the open Euclidean unit ball (use $x/\|x\|$ with zero mapped to zero). Put $k=\lfloor d/16\rfloor$. For a bounded-density probability $\nu$ ($\nu\le H\sigma_d$ for some $H>0$), define

$$
J_\nu(s)=\int\|u-s\|^{-2k}\,d\nu(u),\qquad F(\nu)=D_{\rm KL}(\nu\|\sigma_d)-\int\log J_\nu(s)\,d\nu(s).
$$

The inner integration uses extended nonnegative reciprocal powers; the source uses its real projection inside the logarithm and the real projection of KL. There exist $C>0,d_0$ such that for every $d\ge d_0$, every bounded-density probability satisfies $F(\nu)\ge\frac12D_{\rm KL}(\nu\|\sigma_d)-Cd$. Also $F(\sigma_d)\le2k\log2$, and for every finite collection of bounded-density probabilities $\nu_i$ and nonnegative weights $a_i$ summing to one, $F(\sum_i a_i\nu_i)\le\sum_i a_i F(\nu_i)$.

**Conventions.** Use the spherical reference law, the Riesz potential of order $2\lfloor d/16\rfloor$, the bounded-density domination predicate, and the KL normalization.

## Depends on

- [Spherical kernel potential and outgoing posterior laws](models/gaussian-block-spherical-potential.md)

## Expansion

Uniform small-cap integral estimates and an entropy comparison for the logarithmic potential; convexity concerns the whole difference, not convexity of each term needed separately.

Show the relevant real projections of all integrals are legitimate under bounded density and large dimension. Isolate the reference-law normalization, entropy coercivity, and the finite-mixture convexity proof, retaining zero weights.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianInformation.lean#L200-L200)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/140.md)
- [Accompanying manuscript: Localization costs and information growth for exact Gaussian observations](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Localization-costs-and-information-growth-for-exact-Gaussian-observations-September-27-2026/paper.pdf)
