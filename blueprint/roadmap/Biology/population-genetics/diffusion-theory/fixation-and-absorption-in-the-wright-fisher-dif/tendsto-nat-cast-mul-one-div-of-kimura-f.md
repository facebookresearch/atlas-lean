# Scaled new-mutant limit at fixed α, closed-form version

Let $u$ be a real function of two real variables and $K$ a real function with
$u(\sigma, x) = (1 - e^{-2\sigma x})/(1 - e^{-2\sigma})$ and
$K(\sigma) = 2\sigma/(1 - e^{-2\sigma})$ for $\sigma \ne 0$, $u(0, x) = x$ for every $x$, and
$K(0) = 1$; these are [Kimura's fixation probability](../wright-fisher-diffusion/kimura-fixation.md) and its
[slope constant](../wright-fisher-diffusion/kimura-slope.md). Then for every real $\alpha$, $M\, u(\alpha, 1/M) \to K(\alpha)$ as
$M \to \infty$ through the natural numbers. With $M$ gene copies, $1/M$ is the frequency of a single
new copy and $\alpha$ the scaled selection coefficient. The hypotheses determine $u$ and $K$, so the
result is the concrete limit

$$M\, u_\alpha(1/M) \to K_\alpha = \frac{2\alpha}{1 - e^{-2\alpha}} \quad (\alpha \ne 0), \qquad M\, u_0(1/M) = 1 = K_0,$$

for Kimura's fixation probability $u_\alpha$ and its slope constant $K_\alpha$.
