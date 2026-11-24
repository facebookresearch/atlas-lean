# Stationary law of the Wright–Fisher diffusion with dominance and mutation

With genotype fitnesses giving the drift $2cx(1 - x)(h + (1 - 2h)x)$, where $c = Ns$ and time is in units of $2N$ generations, and mutation rates $\theta_1, \theta_2 > 0$, the Wright–Fisher diffusion has generator $Lf = \frac12x(1 - x)f'' + [2cx(1 - x)(h + (1 - 2h)x) + \frac12(\theta_1(1 - x) - \theta_2x)]f'$, and its stationary law has density

$$\pi(x) = Z^{-1}x^{\theta_1 - 1}(1 - x)^{\theta_2 - 1}\exp\bigl(4chx + 2c(1 - 2h)x^2\bigr), \qquad 0 < x < 1,$$

with $Z$ the normalizing constant. This is the speed density $e^{\bar\sigma}\pi_0$ of Song and Steinrücken (2012, equations (29)–(31)), with $\pi_0(x) = x^{\theta_1 - 1}(1 - x)^{\theta_2 - 1}$ and mean fitness function $\bar\sigma(x) = 2\sigma x[x + 2h(1 - x)] = 4\sigma hx + 2\sigma(1 - 2h)x^2$ at $\sigma = c$. The derivation: with $a(x) = x(1 - x)$, the selection part of $2b/a$ is $4c(h + (1 - 2h)x)$, whose integral is $4chx + 2c(1 - 2h)x^2$, and the mutation part gives $x^{\theta_1 - 1}(1 - x)^{\theta_2 - 1}$ after division by $a$; so $\pi$ solves the zero-current equation $\frac12(a\pi)' = b\pi$, and $\pi$ is integrable because $\theta_1, \theta_2 > 0$. The same convention covers directional selection ($0 \le h \le 1$) and over- and underdominance; at $h = \frac12$ the exponent is $2cx$, genic selection with scaled coefficient $c$.

## Depends on

- [Drift of an allele under selection with dominance](../../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/dominance-drift.md)
- [Wright's stationary density solves the zero-flux equation](../../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion/deriv-flux-wright-density.md)

## Expansion

1. The speed density $\frac{2}{a}\exp(\int2b/a)$ and the exponent $4chx + 2c(1 - 2h)x^2$.
2. Integrability for $\theta_1, \theta_2 > 0$.
3. The zero-current stationary forward equation and uniqueness of the stationary law.
4. Special cases: genic selection at $h = \frac12$, and an interior mode under overdominance.

## Sources

- Y. S. Song and M. Steinrücken, A simple method for finding explicit analytic transition densities of diffusion processes with general diploid selection, Genetics 190 (2012), 1117–1129, equations (26)–(31). <https://doi.org/10.1534/genetics.111.136929>
