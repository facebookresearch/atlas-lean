# Defocusing flow under Gaussian data is not almost surely global

For every $p_0\ge0$ there are an odd integer $p\ge\max(3,p_0)$ and an integer $k>8$ such that for every real $\alpha>k+6$ it is **not** true that the maximal interaction domain $D_f$ equals $\mathbb R$ for almost every datum $f$ under the [weighted Gaussian law](positive-probability-for-gaussian-data.md). Here $D_f$ is the union of the two-sided [interaction intervals for the same defocusing equation](stable-finite-time-blowup.md). The statement negates almost-sure all-real-time continuation, not almost-sure existence or a claim that almost every datum blows up.

## Depends on

- [Gaussian law in weighted Sobolev coordinates](positive-probability-for-gaussian-data.md)
- [Maximal interaction domain](stable-finite-time-blowup.md)

## Proof depends on

- [Positive Gaussian mass of blowup data](positive-probability-for-gaussian-data.md)

## Expansion

For the same $p,k$ and each allowed $\alpha$, use the positive-probability open set where the right endpoint is finite. If all-real-time continuation held almost surely, the set would be contained in a null exceptional set. The argument needs measurability of the open set and does not require silently asserting measurability of the whole set of maximal domains.

## Sources

- OpenAI, [Comparator statement and definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DefocusingNLS.lean#L293-L299) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/371.md).
- OpenAI, [Stable self-similar blowup for a supercritical defocusing Schrödinger equation on the torus](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Stable-Self-Similar-Blowup-for-a-Supercritical-Defocusing-Schrodinger-Equation-on-the-Torus-September-24-2026/paper.pdf) (September 24, 2026), accompanying preprint. The comparator above specifies the selected formal scope.
