# Strict positivity of the finite spherical Laughlin charge gap

For every natural number $n\ge2$ set $Q=3(n-1)$. Then $0<\Delta_{\mathrm c}(Q,n)$.

## Depends on

- [Spherical Laughlin sector energies and gaps](spherical-laughlin-sector-energies.md)

## Proof depends on

- [Strict positivity of the finite neutral gap](spherical-laughlin-neutral-gap-positive.md)
- [Charge–neutral comparison](spherical-laughlin-charge-neutral-gap-comparison.md)

## Proof outline

The real factor $n/(n-1)$ is positive for $n\ge2$, so the positive lower bound supplied by the comparison is strict.

## Sources

- OpenAI Math, [*A Fock-space inequality and the Laughlin spectral gap*, “Charge versus neutral gap at fixed flux”](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/build/sections/06-gap.tex#L102-L122).
- M. Lemm, B. Nachtergaele, S. Warzel, and A. Young, *Recursive spectral relations and the charge vs neutral gap in fractional quantum Hall systems*, Journal of Mathematical Physics **67** (2026), 011901, [doi:10.1063/5.0292975](https://doi.org/10.1063/5.0292975); [arXiv v1](https://arxiv.org/abs/2507.18814v1), Theorem 2.1(I), Lemma 2.3 and (2.10), as cited by the spherical specialization.
- [OpenAI Math: `charge_neutral_gap`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/UniformGap.lean#L18-L27)
- [Positivity from the two inequalities](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/Charge/UniformGap.lean#L57-L72)
