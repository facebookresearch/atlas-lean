# Sawyer–Hartl Poisson random field density

For real numbers $\theta$, $\sigma$ and $x$, let

$$\varphi_{\theta,\sigma}(x) = \frac{\theta\, u_\sigma(1 - x)}{x(1 - x)},$$

with [Kimura's fixation probability](../wright-fisher-diffusion/kimura-fixation.md) $u_\sigma$ and the convention that division by $0$ gives $0$; explicitly, $\varphi_{\theta,\sigma}(x) = \theta(1 - e^{-2\sigma(1 - x)})/((1 - e^{-2\sigma})\, x(1 - x))$ for $\sigma \ne 0$ and $\theta/x$ for $\sigma = 0$ and $x \ne 1$ (at $x = 1$ the defining expression is $0$ for every $\sigma$; the simplification $\theta/x$ does not apply there). For $\theta > 0$ and $x \in (0, 1)$ it is the expected number of sites per unit frequency at which the derived allele has frequency $x$, for scaled mutation rate $\theta = 4Nu$ and scaled genic selection $\sigma = 2Ns$.

## Sources

- S. A. Sawyer and D. L. Hartl, *Population genetics of polymorphism and divergence*, Genetics 132 (1992), 1161–1176.
