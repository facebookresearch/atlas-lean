# Sharp mean extinction time from the quasi-stationary distribution

**Setting.** Let $(X^K_t)$ be a birth-and-death process on $\mathbb Z_+$ with absorbing state $0$ and rates

$$\lambda_n = n\,\tilde\lambda\!\left(\frac nK\right), \qquad \mu_n = n\,\tilde\mu\!\left(\frac nK\right),$$

where $K > 1$ is the carrying-capacity scale. Assume $\tilde\lambda, \tilde\mu$ are positive, differentiable and increasing on $\mathbb R_+$, with $\tilde\lambda(0) > \tilde\mu(0) > 0$ (births prevail at low density) and $\tilde\lambda(x)/\tilde\mu(x) \to 0$ as $x \to \infty$ (deaths prevail at high density). Assume also that there is a unique $x_* > 0$ with $\tilde\lambda(x_*) = \tilde\mu(x_*)$ and $\tilde\lambda'(x_*) \ne \tilde\mu'(x_*)$, that $\int_{x_*/2}^\infty dx/(x\tilde\mu(x)) < \infty$, that $\sup_x \tilde\mu'(x)/\tilde\mu(x) < \infty$, and that $\log(\tilde\mu/\tilde\lambda)$ is increasing. Finally let

$$H(x) = \int_{x_*}^{x} \log\frac{\tilde\mu(s)}{\tilde\lambda(s)}\,ds$$

be three times differentiable with $\sup_x (1+x^2)|H'''(x)| < \infty$. The logistic process $\tilde\lambda \equiv \lambda$, $\tilde\mu(x) = \mu + cx$ is the basic example.

**Theorem.** The process has a unique quasi-stationary distribution $\nu^K$, given by $\nu_n = \pi_n\varphi_n/\langle\varphi,\mathbf 1\rangle_\pi$ with $\pi_n = \lambda_1\cdots\lambda_{n-1}/(\mu_1\cdots\mu_n)$ and $\varphi$ the positive principal eigenvector of the generator on $\ell^2(\pi)$. The principal eigenvalue $-\rho_0(K)$ and the mean extinction time from $\nu^K$ satisfy, for all $K > 1$,

$$\mathbb E_{\nu^K}[T_0] = \frac{1}{\rho_0(K)} = \frac{\sqrt{2\pi}}{\Bigl(\sqrt{\tfrac{\lambda_1}{\mu_1}} - \sqrt{\tfrac{\mu_1}{\lambda_1}}\Bigr)\sqrt{K H''(x_*)}\; x_*\,\tilde\lambda(x_*)}\; \exp\!\Bigl(K\!\int_0^{x_*}\!\log\frac{\tilde\lambda(x)}{\tilde\mu(x)}\,dx\Bigr)\Bigl(1 + O\bigl(\tfrac{(\log K)^3}{\sqrt K}\bigr)\Bigr).$$

Moreover the spectral gap satisfies $\rho_1(K) - \rho_0(K) \ge d/\log K$ for a constant $d > 0$, and for all initial states $n$ and times $t$

$$d_{\mathrm{TV}}\bigl(\mathbb P_n(X^K_t \in \cdot),\ \alpha_n(K)\,\nu^K + (1 - \alpha_n(K))\,\delta_0\bigr) \le C\Bigl(K^{3/2}\log K\, e^{-cK} + (1 - e^{-\rho_0 t}) + K e^{-a t/4} + K^{3/4} e^{c_1 K} e^{-\rho_1 t/2}\Bigr),$$

where $\alpha_n(K)$ is explicit ($\alpha_n = 1$ for $n$ at or above the equilibrium level). So after a time of order $K$ the process is close to the mixture of $\nu^K$ and extinction, and it stays there for a time exponentially large in $K$.

## Expansion

The generator is self-adjoint on $\ell^2(\pi)$ with compact resolvent, so $\rho_0$ is a simple principal eigenvalue. Below the equilibrium level the eigenvector equation is solved as a perturbation $u^0_n(1+\delta_n)$ of the harmonic function $u^0_n = \mathbb P_n(\text{hit the equilibrium level before } 0)$. Above it, $\varphi$ is close to $1$. Matching the two pieces gives an equation whose smallest positive root is $\rho_0$. A Laplace-method evaluation of $\sum_n \pi_n$ around its maximum at $n \approx Kx_*$ produces the $\sqrt{2\pi/(KH''(x_*))}$ prefactor and the exponential factor $e^{-KH(0)}$, since $-H(0) = \int_0^{x_*}\log(\tilde\lambda/\tilde\mu)$. The $1/\log K$ gap comes from a weighted Hardy (Poincaré) inequality.

## Sources

- Jean-René Chazottes, Pierre Collet, Sylvie Méléard, "Sharp asymptotics for the quasi-stationary distribution of birth-and-death processes", arXiv (2014). Section 2 (standing assumptions), Section 3: Theorems 3.1–3.3, Proposition 3.4, Corollary 3.5 (mean time to extinction), Theorem 3.6. <https://doi.org/10.48550/arXiv.1406.1742>. Published version: Probability Theory and Related Fields 164(1-2) (2016), 285–332, <https://doi.org/10.1007/s00440-014-0612-6>; locators above refer to the arXiv version.
