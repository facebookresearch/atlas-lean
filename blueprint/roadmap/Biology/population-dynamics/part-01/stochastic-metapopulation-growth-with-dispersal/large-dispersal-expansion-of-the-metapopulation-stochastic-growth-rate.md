# Large-dispersal expansion of the metapopulation stochastic growth rate

In the patch model $d\mathbf X_t = \mathrm{diag}(\mathbf X_t)(\mu\,dt + \Gamma^\top d\mathbf B_t) + D^\top\mathbf X_t\,dt$ with noise covariance $\Sigma = \Gamma^\top\Gamma$, take dispersal $D = \delta Q$, where $Q$ is an irreducible dispersal matrix with stationary distribution $\pi$, and let $\chi(\delta)$ be the almost sure growth rate of total abundance. The map $\delta \mapsto \chi(\delta)$ is analytic on $(0,\infty)$ and continuous at $\delta = 0$.

**Theorem.** If $Q$ is reversible with respect to $\pi$, then as $\delta \to \infty$

$$\chi(\delta) = \Big(\mu^\top\pi - \tfrac12\pi^\top\Sigma\pi\Big) + \frac1\delta\Big[(\mu - \Sigma\pi)^\top\nu - \frac12\int_0^\infty\mathrm{Tr}\Big(e^{Q^\top s}\,\Pi\,\Sigma\,\Pi\,e^{Qs}\,\Sigma\Big)ds\Big] + O(\delta^{-5/4}),$$

where $\Pi = \mathrm{diag}(\pi) - \pi\pi^\top$ and $\nu$ is the unique vector with $\mathbf 1^\top\nu = 0$ and $Q^\top\nu = -\Pi(\mu - \Sigma\pi)$.

**Corollary.** If $Q$ is symmetric (so $\pi$ is uniform) and commutes with $\Sigma$, let $\lambda_1 \le \cdots \le \lambda_{n-1} < \lambda_n = 0$ be the eigenvalues of $Q$ with orthonormal eigenvectors $\xi_k$, and $\Sigma\xi_k = \theta_k\xi_k$. Then

$$\chi(\delta) = \Big(\bar\mu - \frac{\theta_n}{2n}\Big) - \frac{1}{\delta n}\sum_{k=1}^{n-1}\frac{1}{\lambda_k}\Big((\xi_k^\top\mu)^2 - \frac{\theta_k^2}{4n}\Big) + O(\delta^{-5/4}), \qquad \bar\mu = \frac1n\sum_i\mu_i.$$

Since $\lambda_k < 0$, spatial variation of $\mu$ along the slow dispersal modes raises the growth rate at finite $\delta$, while noise variance along those modes lowers it.

The bracketed coefficient can have either sign: finite dispersal gains from tracking spatial differences in $\mu$ (the $\nu$ term) and loses from reduced averaging of environmental noise (the trace term).

## Depends on

- [Stochastic growth rate of a dispersing population in randomly fluctuating patches](stochastic-growth-rate-of-a-dispersing-population-in-random-patches.md)

## Expansion

For large $\delta$ the patch distribution is $\mathbf Y = \pi + \delta^{-1/2}$-size fluctuations plus a $\delta^{-1}$ drift correction. Linearizing the $\mathbf Y$-equation around $\pi$ gives an Ornstein–Uhlenbeck process driven by $\Pi\Gamma^\top d\mathbf B$ with drift $\delta Q^\top$; its stationary covariance, expressed through $\int_0^\infty e^{Q^\top s}\Pi\Sigma\Pi e^{Qs}ds/\delta$, produces the trace term in $\mathbb E[\mathbf Y^\top\Sigma\mathbf Y]$, while the mean shift solves $Q^\top\nu = -\Pi(\mu - \Sigma\pi)$ and enters linearly through $\mu^\top\mathbb E[\mathbf Y]$. Reversibility gives the self-adjointness needed to control the remainder.

## Sources

- Steven N. Evans, Peter L. Ralph, Sebastian J. Schreiber, Arnab Sen, "Stochastic population growth in spatially heterogeneous environments", arXiv (2011). Section 5 (Proposition 5.1, Theorem 5.2, Corollary 5.3) and Appendices C–E. <https://doi.org/10.48550/arXiv.1105.2280>. Published version: Journal of Mathematical Biology 66(3) (2013), 423–476, <https://doi.org/10.1007/s00285-012-0514-0>; locators above refer to the arXiv version.
