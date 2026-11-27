# Positive Gaussian probability of the same open blowup family

Use the [stable blowup statement](stable-finite-time-blowup.md) with the same equation, Fourier coordinates, and maximal domain. For every $p_0\ge0$ there are an odd integer $p\ge\max(3,p_0)$, an integer $k>8$ and one nonempty open set $U$ of classical finite-time self-similar blowup data as on that page, with the following additional property for every real $\alpha>k+6$.

Let the $g_n$ be independent complex Gaussians, each with independent centered real and imaginary parts of variance $1/2$. On a full product-measure event, $( (1+|n|^2)^{(k-\alpha)/2}g_n )_n$ lies in $\ell^2$; then the sum of its coordinate vectors has physical Fourier coefficient $(1+|n|^2)^{-\alpha/2}g_n$ simultaneously for every $n$. The pushforward law of that sum in the $H^k$ coordinates gives $U$ strictly positive probability. The sum is the source's totalized series in $\ell^2$; summability is part of the conclusion, not a prerequisite on the random draw.

## Depends on

- [Stable finite-time blowup model](stable-finite-time-blowup.md)

## Proof depends on

- [Stable finite-time blowup](stable-finite-time-blowup.md)

## Expansion

Prove the expected squared norm is finite by summing the variances on the twelve-dimensional lattice for $\alpha-k>6$, and justify simultaneous coordinates and measurability of the series. For full support, approximate a target by finitely many coordinates, use positive Gaussian mass in their neighborhood, and use expected tail squared norm and independence for positive remaining tail mass. Apply this to the one open blowup family.

## Sources

- OpenAI, [Comparator statement and definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DefocusingNLS.lean#L35-L291) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/371.md).
- OpenAI, [Stable self-similar blowup for a supercritical defocusing Schrödinger equation on the torus](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Stable-Self-Similar-Blowup-for-a-Supercritical-Defocusing-Schrodinger-Equation-on-the-Torus-September-24-2026/paper.pdf) (September 24, 2026), accompanying preprint. The comparator above specifies the selected formal scope.
