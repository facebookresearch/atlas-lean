# Standardized laws and the third absolute moment

A measure $\mu$ on $\mathbb{R}$ is a standardized law when it is a probability measure with mean
$\int x \, d\mu(x) = 0$ and variance $1$, and has finite third absolute moment
$\int |x|^3 \, d\mu(x) < \infty$. The third absolute moment of $\mu$ is
$\rho(\mu) = \int |x|^3 \, d\mu(x)$.

## Idea

Standardized laws are the laws the Berry–Esseen theorem is stated for after rescaling: a real random
variable with finite third moment and positive variance becomes standardized once its mean is
subtracted and it is divided by its standard deviation, and $\rho$ then becomes the scale-free ratio
$\mathbb{E}|X - \mathbb{E}X|^3/\sigma^3$ that appears in the bound. Finiteness of the third absolute
moment is the same as the identity function lying in $L^3(\mu)$. For a standardized law, Lyapunov's
inequality $(\int x^2 \, d\mu)^{1/2} \le (\int |x|^3 \, d\mu)^{1/3}$ gives $\rho(\mu) \ge 1$; in
particular $\rho(\mu)$ is positive. Examples: the standard Gaussian law, with
$\rho = 2\sqrt{2/\pi} \approx 1.596$, and the symmetric law on $\{-1, 1\}$, with $\rho = 1$.

## Statements

- [Standardized laws with finite third moment](is-standardized-law.md)
- [Third absolute moment](third-moment.md): definition of $\rho(\mu)$, the quantity that the main definition requires to be finite
- [Nonnegativity of the third absolute moment](third-moment-nonnegative.md): basic property of the third absolute moment
- [Standardized laws have an integrable third absolute moment](third-moment-integrable.md): basic property of standardized laws
- [The third absolute moment of a standardized law is positive](third-moment-positive.md): basic property of standardized laws
- [Finite third absolute moment as an $L^3$ condition](mem-lp-three-iff-integrable-abs-cube.md): finite third moment as an L^3 condition
- [The standard Gaussian is a standardized law](standard-gaussian-is-standardized.md): example: the standard Gaussian
