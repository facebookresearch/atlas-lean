# Binomial thinning preserves negative binomial dispersion

Let $X \sim \mathrm{NB}(m, k)$ with $m \ge 0$, $k > 0$, and let each of the $X$ counted events be missed independently with probability $p_u \in [0, 1]$, so that the recorded count is $Y = X - D$ with $D \mid X \sim \mathrm{Binomial}(X, p_u)$. Then

$$Y \sim \mathrm{NB}\big((1 - p_u)\, m,\ k\big):$$

uniform under-counting rescales the mean and leaves the dispersion parameter unchanged.

By contrast, suppose every zero is overlooked with probability $p_z \in [0, 1)$ and replaced by a fresh $\mathrm{NB}(m, k)$ draw, repeating until a value is retained, and write $\pi_x = \mathbb{P}(X = x)$. The retained value $Y'$ has

$$\mathbb{P}(Y' = 0) = \frac{(1 - p_z)\, \pi_0}{1 - p_z \pi_0}, \qquad \mathbb{P}(Y' = x) = \frac{\pi_x}{1 - p_z \pi_0} \quad (x \ge 1),$$

a zero-deflated negative binomial law, which for $m > 0$ and $p_z > 0$ is not of the form $\mathrm{NB}(m', k)$ with the original $k$. (For $m = 0$, $\pi_0 = 1$ and $Y' \equiv 0$, which is $\mathrm{NB}(0, k)$.)

## Depends on

- [Negative-binomial probability generating function](../../superspreading-and-negative-binomial-offspring/nb-pgf.md)
- [Negative-binomial offspring distribution](../../superspreading-and-negative-binomial-offspring/nb-offspring.md)

## Expansion

Thinning composes generating functions: $\mathbb{E}[s^Y] = \mathbb{E}[(p_u + (1 - p_u)s)^X] = G_X(p_u + (1 - p_u)s)$. With $G_X(s) = (1 + (m/k)(1 - s))^{-k}$,

$$G_Y(s) = \left(1 + \frac{m}{k}(1 - p_u)(1 - s)\right)^{-k},$$

which is the generating function of $\mathrm{NB}((1 - p_u)m, k)$. For zero replacement, a final value $x \ge 1$ is reached after $j \ge 0$ rejected zeros with probability $(p_z \pi_0)^j \pi_x$; summing the geometric series gives the stated law, and a retained zero additionally needs one final non-rejection, which gives the factor $1 - p_z$. For $m > 0$ the ratios $\mathbb{P}(Y' = x + 1)/\mathbb{P}(Y' = x) = \pi_{x+1}/\pi_x$ for $x \ge 1$ determine $m$ given $k$, so a match with $\mathrm{NB}(m', k)$ would force $m' = m$, while $\mathbb{P}(Y' = 0) < \pi_0$ because $0 < \pi_0 < 1$. Removing zeros raises the sample mean and lowers the sample variance-to-mean ratio, so by the moment form $\hat k_{\mathrm{mom}} = \bar x^2 / (s^2 - \bar x)$ the estimate of $k$ moves upward; in simulation this bias does not shrink as the sample grows. Uniform under-counting only increases small-sample bias through the smaller mean. If zeros may be under-reported, the remedy is to fit a zero-modified negative binomial model.

## Sources

- J. O. Lloyd-Smith, "Maximum likelihood estimation of the negative binomial dispersion parameter for highly overdispersed data, with applications to infectious diseases", PLoS ONE 2(2) (2007) e180, Methods sections 2.1.2 and 2.1.3, Results sections 3.2 and 3.3, and Discussion, <https://doi.org/10.1371/journal.pone.0000180> (PMC1791715).
