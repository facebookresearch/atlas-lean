# Laughlin charge gap bounds the rescaled neutral gap

For every natural number $n\ge2$ set $Q=3(n-1)$. Then $n\Delta_{\mathrm n}(Q,n)/(n-1)\le\Delta_{\mathrm c}(Q,n)$. The factor $n/(n-1)$ is real.

## Depends on

- [Spherical Laughlin sector energies and gaps](spherical-laughlin-sector-energies.md)

## Proof depends on

- [Equality with the added-particle energy](spherical-laughlin-charge-gap-equals-added-particle-energy.md)

The sector ground kernel has complex dimension one. For a unit vector $x$ in the $(n+1)$-particle sector let $O(x)=\sum_j\|\operatorname{proj}_{K_{Q,n}}a_jx\|^2$. The two inputs are the particle-removal energy recursion $(n-1)\mathcal E_Q(x)\ge\Delta_{\mathrm n}(Q,n)(n+1-O(x))$ at zero $n$-sector ground energy and the rank-one fermionic overlap bound $O(x)\le1$.

## Expansion

Prove the particle-removal norm sum and energy sum, and apply the spectral lower bound off the kernel to the annihilated vectors. Separately derive the overlap bound from the canonical anticommutation relations for a normalized generator of the kernel. Combine the two estimates using nonnegativity of the neutral gap and nonemptiness of the $(n+1)$-sector unit sphere before taking its energy infimum.

## Sources

- OpenAI Math, [*A Fock-space inequality and the Laughlin spectral gap*, “Charge versus neutral gap at fixed flux”](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/build/sections/06-gap.tex#L102-L122).
- M. Lemm, B. Nachtergaele, S. Warzel, and A. Young, *Recursive spectral relations and the charge vs neutral gap in fractional quantum Hall systems*, Journal of Mathematical Physics **67** (2026), 011901, [doi:10.1063/5.0292975](https://doi.org/10.1063/5.0292975); [arXiv v1](https://arxiv.org/abs/2507.18814v1), Theorem 2.1(I), Lemma 2.3 and (2.10), as cited by the spherical specialization.
- [OpenAI Math: `charge_neutral_gap`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/UniformGap.lean#L18-L27)
- [Comparison contracts and deduction](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/Charge/Comparison.lean#L8-L44)
- [Particle-removal recursion](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/Charge/Recursion.lean#L45-L69)
- [Rank-one bound from the fermionic frame estimate](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/Charge/Overlap.lean#L107-L141)
- [Kernel rank and vanishing ground energies](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/Charge/LaughlinGround.lean#L73-L103)
