# Logarithmic Sobolev estimate for the Euclidean half-wave

For every natural $n\ge2$ and real $p,B$ with $2<p$ and $2n+6<B$, set $s=\max(0,(n-1)/2-n/p)$. For one real $C>0$ and every complex Schwartz function $f$, both $J^s[\log(2+J)]^B f$ in space and the half-wave $U(t)f$ on the observation slab belong to the indicated $L^p$ spaces, and

$$
\|U(t)f\|_{L^p(\mathbb R^n\times[1,2])}\le C\|J^s[\log(2+J)]^B f\|_{L^p(\mathbb R^n)}.
$$

Here $U(t)$ and $J$ are the [angular-frequency half-wave and Bessel multipliers](angular-frequency-wave-multipliers.md). The Sobolev order is exactly $s$; the extra loss is logarithmic.

## Depends on

- [Angular-frequency wave multipliers](angular-frequency-wave-multipliers.md).

## Proof depends on

- [Logarithmic frequency-localized estimate](critical-frequency-local-smoothing-logarithmic-loss.md).

## Proof outline

Use interpolation about the critical exponent, frequency decomposition, and summation with a logarithmic loss that remains summable at the stated strict threshold.

Pass from the critical localized estimate to each frequency band at exponent $p$, and sum in the slab norm, including the low-frequency term. Do not replace the logarithmic loss by a positive derivative loss.

## Sources

- OpenAI Math, [`logarithmic_sobolev`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/LocalSmoothing/Main.lean#L19-L21).
- [Named Fourier main-results bundle](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/Main.lean#L11-L21).
- [Family scope and accompanying paper](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/079.md).
- [Definitions in `Definitions.lean`, lines 21–53](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/LocalSmoothing/Definitions.lean#L21-L53).
- [Definitions in `Definitions.lean`, lines 81–91](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/LocalSmoothing/Definitions.lean#L81-L91).
- [Definitions in `Basic.lean`, lines 8–11](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/Wave/Basic.lean#L8-L11).
