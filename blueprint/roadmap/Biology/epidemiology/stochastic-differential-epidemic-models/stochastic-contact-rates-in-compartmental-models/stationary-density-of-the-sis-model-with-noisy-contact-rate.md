# Stationary density of the SIS model with a noisy contact rate

**Model.** Let $X(t) \in [0,1]$ be the infected fraction in an SIS epidemic with recovery rate $\gamma > 0$ and a fluctuating contact rate $\lambda(t) = \bar\lambda + \sigma\xi(t)$, where $\bar\lambda > 0$ and $\sigma > 0$:

$$\frac{dX}{dt} = \bar\lambda X(1-X) - \gamma X + \sigma X(1-X)\,\xi(t).$$

The deterministic model ($\sigma = 0$) has basic reproduction number $R_0 = \bar\lambda/\gamma$ and endemic equilibrium $x_1 = 1 - R_0^{-1}$, which is stable for $R_0 > 1$. Its relaxation time is $\eta = (\bar\lambda - \gamma)^{-1}$.

**Why the contact rate is Ornstein–Uhlenbeck.** Suppose each individual's contact count over a window of length $\Delta t$ changes by $\pm 1$ over a short shift $\delta t$, with probabilities $\tfrac12[(\kappa\Delta t)^2 \pm \theta(\mu\Delta t - i)]\delta t$ when the current count is $i$. This has a constant diffusion and a drift back to the mean. Averaging over $N$ independent individuals and applying the central limit theorem gives the Langevin equation

$$\frac{d\lambda}{dt} = \theta(\mu - \lambda) + \frac{\kappa}{\sqrt N}\,\xi^{\mathrm{WN}}(t).$$

So $\lambda$ is a stationary Ornstein–Uhlenbeck process with mean $\mu$ and covariance $\frac{\sigma^2}{2\tau}e^{-|t-s|/\tau}$, where $\tau = 1/\theta$ and $\sigma = \kappa\tau/\sqrt N$. White noise is the limit $\tau \to 0$.

**Proposition (white noise).** If $\xi$ is standard Gaussian white noise and $R_0 > 1$, the stationary density of $X$ is

$$p_0(x) = C\,x^{\frac{2(1-R_0^{-1})}{\sigma^2/\bar\lambda} - 2 + \varpi}\,(1-x)^{-\frac{2(1-R_0^{-1})}{\sigma^2/\bar\lambda} - 2 + \varpi}\exp\!\Big(-\frac{2R_0^{-1}}{\sigma^2/\bar\lambda}\,\frac{1}{1-x}\Big), \qquad 0 < x < 1,$$

with $\varpi = 0$ for the Itô interpretation and $\varpi = 1$ for Stratonovich, and $C$ the normalizing constant when the density is integrable. It depends only on $R_0$ and the relative noise variance $\sigma^2/\bar\lambda$.
- Itô: the density is integrable at $0$, so the infection persists, if and only if $\sigma^2/\bar\lambda < 2(1 - R_0^{-1})$, that is $R_0 - \sigma^2/(2\gamma) > 1$. Otherwise the stationary law is $\delta_0$, so enough noise eliminates the infection whatever $R_0$ is.
- Stratonovich: the infection is never certainly eliminated when $R_0 > 1$.
- In both interpretations the density changes shape as the noise grows (noise-induced transitions). For $1 < R_0 < 2$ the nonzero mode drifts toward $0$ as $\sigma^2/\bar\lambda$ increases. For $R_0 > 2$ it drifts toward $1$, and a second mode appears at $0$. For $1 < R_0 < 1.5$ the density stays unimodal; for $1.5 < R_0 < 2$ it passes through a bimodal stage.

**Proposition (OU noise, approximate).** If $\xi$ is a standard OU process with correlation time $\tau$, the nonlinear Fokker–Planck approximation gives the closed-form stationary density

$$p_0(x) = C\,x^{Q_1}(1-x)\,(Gx^2 - Dx + F)^{Q_2}\exp\!\Big[Q_3\arctan\frac{2Gx - D}{\sqrt{|\Delta|}}\Big],$$

with

$$a = \tau(\bar\lambda - \gamma),\quad A = \frac{a}{1+a},\quad B = \frac{R_0}{R_0 - 1},\quad P = \frac{2(1+a)}{B\,\sigma^2/\bar\lambda},$$

$$G = A^2B^2 + AB + 1,\quad D = A + AB + 2A^2B + 2,\quad F = A^2 + A + 1,\quad |\Delta| = 4GF - D^2 > 0,$$

$$Q_1 = \frac{P}{F} - 1,\quad Q_2 = -\frac{P}{2F} - 1,\quad Q_3 = \frac{P(D - 2BF)}{F\sqrt{|\Delta|}}.$$

It depends on $R_0$, $\sigma^2/\bar\lambda$ and the relative correlation time $a = \tau/\eta$, and it reduces to the Stratonovich white-noise density as $\tau \to 0$. Temporal correlation strongly delays the noise-induced transitions, so white noise systematically underestimates disease severity.

## Proof sketch

For white noise the stationary Fokker–Planck solution is $p_0 \propto g^{\varpi-2}\exp\big(2\int f/g^2\big)$, with drift $f(x) = x(\bar\lambda(1-x) - \gamma)$ and diffusion coefficient $g(x) = \sigma x(1-x)$. Partial fractions give

$$\frac{f}{g^2} = \frac{1}{\sigma^2}\Big[\frac{\bar\lambda - \gamma}{x} + \frac{\bar\lambda - \gamma}{1-x} - \frac{\gamma}{(1-x)^2}\Big].$$

Integrating gives the power-law factors with exponent $\pm 2(\bar\lambda - \gamma)/\sigma^2$ and the factor $\exp(-2\gamma/(\sigma^2(1-x)))$. Near $x = 0$ the Itô density behaves like $x^{2(\bar\lambda-\gamma)/\sigma^2 - 2}$, which is integrable exactly when $\sigma^2 < 2(\bar\lambda - \gamma)$. This is the Gray et al. persistence threshold. The modes are the roots of a quadratic, and their bifurcation curves in the $(R_0, \sigma^2/\bar\lambda)$ plane separate the unimodal, bimodal and zero-mode regimes. For OU noise, the correlated-noise Fokker–Planck closure replaces $g^2$ by an effective diffusion that depends on $a$. The resulting rational integrand has a quadratic denominator $Gx^2 - Dx + F$ with negative discriminant, which produces the arctan term.

## Sources

- Konstantinos Mamis and Mohammad Farazmand, "Modeling correlated uncertainties in stochastic compartmental models", *Mathematical Biosciences* 374 (2024), 109226, <https://doi.org/10.1016/j.mbs.2024.109226>. Preprint version: arXiv:2307.06866 (2023), Section 2 (contact-rate transition probabilities and the OU Langevin equation), Section 3.1 (white-noise stationary density, the persistence condition and noise-induced transitions), Section 3.2 (approximate OU stationary density) and the appendices on the Fokker–Planck calculations, <https://doi.org/10.48550/arXiv.2307.06866>.
