# Logarithmic loss for frequency-localized critical local smoothing

For every natural dimension $n\ge2$, set $p_c=2n/(n-1)$. Let $\phi:\mathbb R^n\to\mathbb C$ be smooth with compact support and $0\notin\operatorname{supp}\phi$ (closed support). For each such $n,\phi$ there is a real $C>0$ working for every $0<h\le1$ and complex Schwartz function $f$.

Use the [angular-frequency transform and observation measure](angular-frequency-wave-multipliers.md), and let $V_{\phi,h}f(x,t)=\mathcal F^{-1}[e^{-it|\xi|}\phi(h\xi)\widehat f(\xi)](x)$. Then $V_{\phi,h}f$ belongs to $L^{p_c}$ on the observation slab and

$$
\|V_{\phi,h}f\|_{L^{p_c}(\mathbb R^n\times[1,2])}\le C(1+\log(1/h))^{2n+5}\|f\|_{L^{p_c}(\mathbb R^n)}.
$$

There is no dyadic restriction on $h$ and no positivity assumption on the cutoff.

## Depends on

- [Angular-frequency wave multipliers](angular-frequency-wave-multipliers.md).

## Proof depends on

A uniform positive packet-solvability and packet-to-oscillatory-integral transfer theorem at the critical exponent, with the exact logarithmic exponent and observation slab.

## Expansion

Split the packet construction and positive solvability from the finite scale assembly and the continuous Fourier transfer. The frequency-localized bound with a power loss would not give this endpoint.

## Sources

- OpenAI Math, [`logarithmic_refinement`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/LocalSmoothing/Main.lean#L10-L12).
- [Named Fourier main-results bundle](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/Main.lean#L11-L21).
- [Family scope and accompanying paper](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/079.md).
- [Definitions in `Definitions.lean`, lines 21–53](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/LocalSmoothing/Definitions.lean#L21-L53).
- [Definitions in `Definitions.lean`, lines 68–79](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/LocalSmoothing/Definitions.lean#L68-L79).
- [Definitions in `Basic.lean`, lines 8–11](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/Wave/Basic.lean#L8-L11).
