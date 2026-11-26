# Strict positivity of the finite spherical Laughlin neutral gap

For every natural number $n\ge2$ set $Q=3(n-1)$. Then $0<\Delta_{\mathrm n}(Q,n)$.

## Depends on

- [Spherical Laughlin sector energies and gaps](spherical-laughlin-sector-energies.md)

## Proof depends on

The Laughlin zero-mode identification in occupation coordinates: $K_{Q,n}$ is a line. The $n$-particle sector has dimension greater than one, so its unit sphere orthogonal to that line is nonempty.

## Expansion

Separate the kernel identification (normalized tensor–exterior representation and polynomial pair-vanishing) from the finite-dimensional minimization lemma. The energy is strictly positive at each orthogonal unit vector and attains its minimum there. Pointwise positivity alone would not prove a positive infimum without the compactness argument.

## Sources

- OpenAI Math, [*A Fock-space inequality and the Laughlin spectral gap*, “Charge versus neutral gap at fixed flux”](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/build/sections/06-gap.tex#L102-L122).
- [OpenAI Math: `charge_neutral_gap`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/UniformGap.lean#L18-L27)
- [Occupation zero-mode identification](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/Charge/LaughlinGround.lean#L50-L83)
- [Nonempty excited unit sphere](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/Charge/FiniteGap.lean#L69-L85)
- [Strictly positive compact minimum](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Laughlin/Charge/FiniteGap.lean#L95-L135)
