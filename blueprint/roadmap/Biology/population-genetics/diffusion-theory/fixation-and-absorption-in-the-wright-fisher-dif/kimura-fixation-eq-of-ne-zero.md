# Closed form of Kimura's fixation probability for nonzero σ

For all real $\sigma \ne 0$ and $x$,
[Kimura's formula](../wright-fisher-diffusion/kimura-fixation.md) is

$$u_\sigma(x) = \frac{1 - e^{-2\sigma x}}{1 - e^{-2\sigma}}.$$

It is a fixation probability only for an initial frequency $x \in [0, 1]$: since $u_\sigma(1) = 1$
and $u_\sigma$ is strictly increasing, $u_\sigma(x) > 1$ for $x > 1$. With
$\sigma_{\mathrm{Moran}} = 2\sigma$ this is the
[closed form in the Moran normalization](../../moran-model/kimura-fixation-half.md).
