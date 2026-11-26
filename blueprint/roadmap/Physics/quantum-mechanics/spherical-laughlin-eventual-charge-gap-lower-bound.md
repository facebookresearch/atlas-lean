# Eventual lower bound for the spherical Laughlin charge gap

There is a natural number $n_0\ge2$ such that for every natural number $n\ge n_0$, with $Q=3(n-1)$,

$$
\frac{n}{25(n-1)}\le\Delta_{\mathrm c}(Q,n).
$$

The quotient is real; the threshold applies only to this quantitative clause.

## Depends on

- [Spherical Laughlin sector energies and gaps](spherical-laughlin-sector-energies.md)

## Proof depends on

- [Charge–neutral comparison](spherical-laughlin-charge-neutral-gap-comparison.md)
- [Spherical Fock-space operator gap](spherical-laughlin-fock-operator-gap.md)
- [Finite neutral-gap positivity](spherical-laughlin-neutral-gap-positive.md), to guarantee the orthogonal unit sector is nonempty.

## Proof outline

The [finite neutral-gap positivity result](spherical-laughlin-neutral-gap-positive.md) makes the orthogonal unit sector nonempty because the real infimum of the empty set is zero. Take the admissible Fock-space coefficient $1/25$ and restrict the eigenvalue bound to the invariant $n$-particle sector, with $Q$ eventually above the flux cutoff. Every unit vector perpendicular to the sector kernel then has energy at least $1/25$. Take the infimum and apply the comparison. Strict positivity is used only for nonemptiness, not as a uniform estimate.

## Sources

- OpenAI Math, [*A Fock-space inequality and the Laughlin spectral gap*, “Charge versus neutral gap at fixed flux”](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/build/sections/06-gap.tex#L102-L122).
- M. Lemm, B. Nachtergaele, S. Warzel, and A. Young, *Recursive spectral relations and the charge vs neutral gap in fractional quantum Hall systems*, Journal of Mathematical Physics **67** (2026), 011901, [doi:10.1063/5.0292975](https://doi.org/10.1063/5.0292975); [arXiv v1](https://arxiv.org/abs/2507.18814v1), Theorem 2.1(I), Lemma 2.3 and (2.10), as cited by the spherical specialization.
- [OpenAI Math: `charge_neutral_gap`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/UniformGap.lean#L18-L27)
- [Neutral-gap transfer and eventual charge bound](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/Charge/UniformGap.lean#L10-L75)
- [From the neutral coefficient to the charge coefficient](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/Charge/Comparison.lean#L46-L58)
- [Sharp spherical coefficient and eigenvalue implication](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/Fock/SharpGap.lean#L62-L85)
