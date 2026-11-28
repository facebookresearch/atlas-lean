# Separable static heterogeneity by redefining the depletion function

Let hosts carry a static trait $x$ in a measurable space $\Omega$ with population distribution $\Phi$, and let $s(t, x)$ be the probability that a host with trait $x$ is still susceptible at time $t$, with $s(-\infty, x) = 1$. The heterogeneous Kermack–McKendrick model is

$$\partial_t s(t,x) = -F(t,x)\, s(t,x), \qquad F(t,x) = N \int_0^\infty \!\! \int_\Omega A(\tau, x, \xi)\, F(t-\tau, \xi)\, s(t-\tau, \xi)\, \Phi(d\xi)\, d\tau,$$

where $A(\tau, x, \xi)$ is the contribution of a host with trait $\xi$, infected $\tau$ time units ago, to the force of infection on a host with trait $x$.

**Proposition (separable mixing).** Suppose $A(\tau, x, \xi) = a(x)\, b(\tau)\, c(\xi)$, with relative susceptibility $a$ and relative infectiousness $c$. Then $\int_{-\infty}^t F(\sigma, x)\, d\sigma = a(x)\, w(t)$ for a scalar $w$, $s(t,x) = e^{-a(x) w(t)}$, and

$$w(t) = \int_0^\infty b(\tau)\, \Psi\bigl(w(t-\tau)\bigr)\, d\tau, \qquad \Psi(w) = N \int_\Omega c(\xi)\bigl(1 - e^{-a(\xi) w}\bigr) \Phi(d\xi).$$

If moreover $b(\tau) = U e^{\tau\Sigma} V$, the [integrated compartmental system](integrated-form-of-compartmental-epidemic-models.md) $\dot Q = \Sigma Q + V\Psi(UQ)$, $w = UQ$, holds unchanged except for the new $\Psi$: separable heterogeneity is incorporated without increasing the dimension.

**Standard form.** Normalize $a(\bar x) = c(\bar x) = 1$ at a reference trait $\bar x$ and let $\bar s(t) = s(t, \bar x)$, so $w = -\log \bar s$ and $s(t,x) = \bar s(t)^{a(x)}$. With $Y(t) = N\int_\Omega c(\xi)\, y(t,\xi)\, \Phi(d\xi)$ the infectiousness-weighted state vector, the heterogeneous system has the standard form

$$\frac{d\bar s}{dt} = -\bar F \bar s, \qquad \frac{dY}{dt} = \Sigma Y + \bar F\, \Psi'(-\log \bar s)\, V, \qquad \bar F = UY,$$

with $\Psi'(w) = N \int_\Omega c(\xi)\, a(\xi)\, e^{-a(\xi) w}\, \Phi(d\xi)$. The fraction still susceptible is $s_{\mathrm{tot}} = \int_\Omega \bar s^{\,a(\xi)} \Phi(d\xi)$.

## Depends on

- [Integrated form of compartmental epidemic models](integrated-form-of-compartmental-epidemic-models.md)

## Expansion

Under separability, $F(t,x)$ is $a(x)$ times a function of time, so the infinite-dimensional state collapses to the scalar $w$. Integrating the constitutive equation in time and replacing $Fs$ by $-\partial_t s$ gives the scalar renewal equation with the trait-averaged depletion function $\Psi$. When $a \equiv c \equiv 1$ it reduces to $\Psi(w) = N(1 - e^{-w})$. When $a \equiv 1$ only the mean of $c$ matters: heterogeneity in infectiousness alone is invisible in the deterministic large-population limit. The standard form follows by differentiating the integrated system, $\dot Y = \Sigma Y + \Psi'(UQ)\, UY\, V$, and identifying $UQ = -\log \bar s$.

## Sources

- O. Diekmann and H. Inaba, "A systematic procedure for incorporating separable static heterogeneity into compartmental epidemic models", *Journal of Mathematical Biology* (2023), <https://doi.org/10.1007/s00285-023-01865-0> (PMC9839824; Sections 5 and 6, Equations (5.1)–(5.7) and (6.1)–(6.10)).
