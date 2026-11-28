# Gaussian approximation of the quasi-stationary distribution

Work under the hypotheses of [Sharp mean extinction time from the quasi-stationary distribution](sharp-mean-extinction-time-from-the-quasi-stationary-distribution.md): a birth-and-death process with rates $\lambda_n = n\tilde\lambda(n/K)$, $\mu_n = n\tilde\mu(n/K)$, a unique deterministic equilibrium density $x_*$ with $\tilde\lambda(x_*) = \tilde\mu(x_*)$, and

$$H(x) = \int_{x_*}^{x}\log\frac{\tilde\mu(s)}{\tilde\lambda(s)}\,ds, \qquad H''(x_*) = \frac{\tilde\mu'(x_*) - \tilde\lambda'(x_*)}{\tilde\lambda(x_*)} > 0 .$$

**Theorem.** Let $\nu^K$ be the unique quasi-stationary distribution and $n_*(K)$ the integer equilibrium level near $Kx_*$. Define the discrete Gaussian

$$G^K_n = \frac{1}{Z(K)}\exp\!\left(-\frac{(n - n_*(K))^2}{2K\sigma^2}\right), \qquad \sigma = \frac{1}{\sqrt{H''(x_*)}},$$

with $Z(K) = \sum_{n \ge 1} e^{-(n-n_*(K))^2/(2K\sigma^2)} = \sqrt{2\pi K}\,\sigma + O(1)$. Then

$$d_{\mathrm{TV}}\bigl(\nu^K, G^K\bigr) \le \frac{C}{\sqrt K} \qquad \text{for all } K > 1 .$$

So, conditioned on survival, the population fluctuates around $Kx_*$ with Gaussian fluctuations of order $\sqrt K$ and variance $K/H''(x_*)$. This is the variance of the stationary linear-noise (Ornstein–Uhlenbeck) approximation at the equilibrium.

## Depends on

- [Sharp mean extinction time from the quasi-stationary distribution](sharp-mean-extinction-time-from-the-quasi-stationary-distribution.md)

## Expansion

Since $\nu_n \propto \pi_n\varphi_n$ and the principal eigenvector $\varphi$ is uniformly close to an explicit profile that equals $1$ above the equilibrium and decays only near $0$, the shape of $\nu^K$ is that of $\pi_n$ away from $0$. Taking logarithms, $\log\pi_n = -K H(n/K) + O(\log n)$. Expanding $H$ to second order at $x_*$ gives the Gaussian with variance $K/H''(x_*)$, and the bound on $H'''$ controls the remainder at the scale $|n - Kx_*| \lesssim \sqrt K\log K$. The mass outside this window is exponentially small in $K$.

## Sources

- Jean-René Chazottes, Pierre Collet, Sylvie Méléard, "Sharp asymptotics for the quasi-stationary distribution of birth-and-death processes", arXiv (2014). Section 3, Theorem 3.7; proof in Section 8. <https://doi.org/10.48550/arXiv.1406.1742>. Published version: Probability Theory and Related Fields 164(1-2) (2016), 285–332, <https://doi.org/10.1007/s00440-014-0612-6>; locators above refer to the arXiv version.
