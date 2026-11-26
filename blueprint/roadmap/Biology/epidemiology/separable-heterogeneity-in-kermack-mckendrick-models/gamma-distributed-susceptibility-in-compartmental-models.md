# Gamma-distributed susceptibility in compartmental models

In the [separable heterogeneous Kermack–McKendrick model](separable-static-heterogeneity-by-redefining-the-depletion-function.md) take $\Omega = [0, \infty)$, relative susceptibility $a(x) = x$, and $\Phi$ the gamma distribution with mean $1$ and variance $1/p$, with density

$$x \mapsto \frac{p^p}{\Gamma(p)}\, x^{p-1} e^{-px}, \qquad p > 0.$$

Its Laplace transform is $\hat\Phi(\lambda) = (1 + \lambda/p)^{-p}$.

**Closed-form depletion functions.**

$$\Psi(w) = N\Bigl[1 - \Bigl(1 + \frac{w}{p}\Bigr)^{-p}\Bigr] \quad \text{if } c \equiv 1, \qquad \Psi(w) = N\Bigl[1 - \Bigl(1 + \frac{w}{p}\Bigr)^{-p-1}\Bigr] \quad \text{if } c(\xi) = \xi.$$

**Standard form in the total susceptible fraction.** With reference trait $\bar x = 1$ the total susceptible fraction is $s_{\mathrm{tot}} = \hat\Phi(w)$, and the compartmental system becomes

$$\frac{ds_{\mathrm{tot}}}{dt} = -\bar F\, s_{\mathrm{tot}}^{1 + 1/p}, \qquad \frac{dY}{dt} = \Sigma Y + \bar F\, H(s_{\mathrm{tot}})\, V, \qquad \bar F = UY,$$

with

$$H(s) = N s^{1 + 1/p} \quad \text{if } c \equiv 1, \qquad H(s) = N\Bigl(1 + \frac1p\Bigr) s^{1 + 2/p} \quad \text{if } c(\xi) = \xi.$$

As $p \to \infty$ (no heterogeneity) these reduce to the homogeneous model.

## Depends on

- [Separable static heterogeneity by redefining the depletion function](separable-static-heterogeneity-by-redefining-the-depletion-function.md)

## Proof depends on

- [Moment generating function of the gamma distribution](../../../Probability/distributions/continuous/gamma-distribution/gamma-mgf/mgf-gamma-measure-of-lt.md): at shape $p$ and rate $p$ with argument $-w$, giving $\int e^{-\xi w}\Phi(d\xi) = (1 + w/p)^{-p}$, and at shape $p + 1$ and rate $p$, giving $\int \xi e^{-\xi w}\Phi(d\xi) = (1 + w/p)^{-p-1}$.

## Expansion

With $a(\xi) = \xi$, $\Psi(w) = N\int c(\xi)(1 - e^{-\xi w})\Phi(d\xi)$ is expressed through $\hat\Phi$ and its derivatives: $\int e^{-\xi w}\Phi(d\xi) = (1 + w/p)^{-p}$ and $\int \xi e^{-\xi w}\Phi(d\xi) = (1 + w/p)^{-p-1}$, which gives both closed forms; the second holds because $\xi\,\Phi(d\xi)$ is the gamma distribution with shape $p + 1$ and rate $p$, the mean of $\Phi$ being $1$. Since $\dot w = \bar F$, $\dot s_{\mathrm{tot}} = \hat\Phi'(w)\bar F = -(1 + w/p)^{-p-1}\bar F = -\bar F s_{\mathrm{tot}}^{1+1/p}$, and $\Psi'(w)$ written as a power of $s_{\mathrm{tot}}$ gives $H$. The power-law depletion $s^{1+1/p}$ is the classical device for gamma-distributed frailty in epidemic models, here derived systematically and valid for any compartmental structure $(U, \Sigma, V)$.

## Sources

- O. Diekmann and H. Inaba, "A systematic procedure for incorporating separable static heterogeneity into compartmental epidemic models", *Journal of Mathematical Biology* (2023), <https://doi.org/10.1007/s00285-023-01865-0> (PMC9839824; Section 7, Equations (7.1)–(7.7)).
