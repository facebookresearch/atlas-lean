# Extension from the truncated forward light cone

In natural spatial dimension $n\ge2$, put $\Sigma=\{(\rho\omega,\rho):1\le\rho\le2,\ |\omega|=1\}$, with the pushforward of $\sqrt2\rho^{n-1}\,d\rho\,d\sigma(\omega)$, where $d\sigma$ is the spherical surface measure obtained from Euclidean volume. The extension of an ambient complex-valued function $g$ is

$$
Eg(x,t)=\int_\Sigma e^{i(x\cdot\xi+t\tau)}g(\xi,\tau)\,d\sigma_\Sigma(\xi,\tau).
$$

For each extended input exponent $a>1$ (including $a=\infty$) and each real $b$ satisfying both $b>2n/(n-1)$ and $b>((n+1)/(n-1))a'$, where $a'=a/(a-1)$ if finite and $a'=1$ at infinity, there is a real $C>0$ such that every $g\in L^a(\sigma_\Sigma)$ has $Eg\in L^b(\mathbb R^{n+1})$ and $\|Eg\|_b\le C\|g\|_{L^a(\sigma_\Sigma)}$. The target uses product Lebesgue measure on all of space-time.

## Depends on

The stated weighted radial/spherical pushforward, with the angular-frequency extension phase and the $a=\infty$ conjugate convention.

## Proof depends on

- [Spherical extension in the strict mixed range](../spherical-extension-strict-mixed-range.md).

## Proof outline

Prove the radial diagonal estimate for the cone from the spherical estimate, then transfer it to the strict mixed range on the finite cone surface measure.

Keep the Gram density $\sqrt2\rho^{n-1}$, check measurability and $L^a$ data on the ambient representation, and retain the strict bounds before the diagonal-to-mixed step. The sphere result is an antecedent, not the same operator.

## Sources

- OpenAI Math, [`cone_extension`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/Cone/Main.lean#L10-L11).
- [Named Fourier main-results bundle](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/Main.lean#L11-L21).
- [Family scope and accompanying paper](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/079.md).
- [Definitions in `Extension.lean`, lines 49–58](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/Cone/Extension.lean#L49-L58).
- [Definitions in `Geometry.lean`, lines 9–18](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/Cone/Geometry.lean#L9-L18).
- [Definitions in `Measure.lean`, lines 11–81](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/Cone/Measure.lean#L11-L81).
- [Definitions in `Definitions.lean`, lines 16–24](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/Restriction/Definitions.lean#L16-L24).
- [Definitions in `Basic.lean`, lines 8–11](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/Wave/Basic.lean#L8-L11).
