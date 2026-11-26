# Laughlin charge gap equals the added-particle ground energy

For every natural number $n\ge2$ set $Q=3(n-1)$. Then $\Delta_{\mathrm c}(Q,n)=E_0(Q,n+1)$.

## Depends on

- [Spherical Laughlin sector energies and gaps](spherical-laughlin-sector-energies.md)

## Proof depends on

A zero-energy unit vector in the $n$-particle sector at this flux, and the transfer of zero ground energy to the $(n-1)$-particle sector by fermionic annihilation.

## Expansion

Transport the nonzero Laughlin polynomial vector into normalized occupation coordinates, prove its energy is zero, and normalize it. Isolate the number and energy identities for annihilating one particle; they give at least one nonzero annihilation of the zero-energy vector, still of zero energy. The two zero ground energies then cancel in the charge second difference.

## Sources

- OpenAI Math, [*A Fock-space inequality and the Laughlin spectral gap*, “Charge versus neutral gap at fixed flux”](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/build/sections/06-gap.tex#L102-L122).
- [OpenAI Math: `charge_neutral_gap`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/UniformGap.lean#L18-L27)
- [Ground-sector zero energies](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/Charge/LaughlinGround.lean#L85-L103)
- [Zero energy in the predecessor sector](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/Charge/Recursion.lean#L71-L100)
- [Equality from the two zero energies](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/Charge/Comparison.lean#L23-L30)
