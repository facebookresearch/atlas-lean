# Logarithmic wave estimate for displacement and velocity data

Let $n\ge2$ be natural and $p,B$ real with $2<p$ and $2n+6<B$. For complex Schwartz functions $f,g$ on $\mathbb R^n$, take the Fourier solution with displacement $f$ and velocity $g$, using the [angular-frequency convention](angular-frequency-wave-multipliers.md):

$$
u(x,t)=\mathcal F^{-1}\!\left[\cos(t|\xi|)\widehat f(\xi)+\frac{\sin(t|\xi|)}{|\xi|}\widehat g(\xi)\right](x).
$$

The second multiplier has value $t$ at zero frequency. Set $s=\max(0,(n-1)/2-n/p)$. There is a real $C>0$, independent of $f,g$, satisfying

$$
\|u\|_{L^p(\mathbb R^n\times[1,2])}\le C\left(\|J^s[\log(2+J)]^B f\|_{L^p}+\|J^{s-1}[\log(2+J)]^B g\|_{L^p}\right).
$$

This is the bound in extended $L^p$ norms, with the one-derivative shift only for velocity.

## Depends on

- [Angular-frequency wave multipliers](angular-frequency-wave-multipliers.md).

## Proof depends on

- [Logarithmic Sobolev half-wave estimate](half-wave-logarithmic-sobolev-estimate.md).

## Proof outline

Separate the cosine term, high-frequency velocity (shift by one derivative), and the low-frequency velocity estimate for the regularized sine quotient.

Check the multiplier identity at zero and combine the three estimates on the exact product measure. The positive-half-wave estimate does not itself state this two-data bound.

## Sources

- OpenAI Math, [`wave_data`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/PDE/WaveEquation/Main.lean#L10-L12).
- [Named Fourier main-results bundle](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/Main.lean#L11-L21).
- [Family scope and accompanying paper](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/079.md).
- [Definitions in `Definitions.lean`, lines 21–53](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/LocalSmoothing/Definitions.lean#L21-L53).
- [Definitions in `Basic.lean`, lines 8–11](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/Wave/Basic.lean#L8-L11).
- [Definitions in `Estimate.lean`, lines 10–31](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/PDE/WaveEquation/Estimate.lean#L10-L31).
- [Definitions in `Formula.lean`, lines 74–77](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/PDE/WaveEquation/Formula.lean#L74-L77).
