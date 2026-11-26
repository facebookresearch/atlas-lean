# Identifiability of directed interactions from structure factors

**Model.** Fluctuations $u(x,t) \in \mathbb{R}^K$ of $K$ populations around a stationary homogeneous state obey the linear stochastic reaction-diffusion equation

$$\partial_t u = Au + D\nabla^2u + \xi, \qquad \mathbb{E}\bigl[\xi(x,t)\xi(x',t')^\top\bigr] = \Sigma\,\delta(x-x')\delta(t-t'),$$

with interaction (Jacobian) matrix $A$, diagonal motilities $D \ge 0$ and symmetric positive definite noise covariance $\Sigma$. In Fourier space $\partial_t\hat u = M(k)\hat u + \hat\xi$ with $M(k) = A - |k|^2D$, assumed Hurwitz for all $k$. The observable is the stationary structure factor $S(k)$, the unique solution of the Lyapunov equation

$$M(k)S(k) + S(k)M(k)^\top + \Sigma = 0 .$$

Write $A = A_s + A_a$ (symmetric and antisymmetric parts).

**Time-scale invariance.** $\Phi(A,D,\Sigma) = \Phi(cA,cD,c\Sigma)$ for every $c > 0$, so with $\Sigma$ unknown the absolute time scale is never identifiable.

**Perturbations.** For fixed $(D,\Sigma)$, $A \mapsto A + J$ leaves every $S(k)$ unchanged iff $JS(k) + S(k)J^\top = 0$ for all $k$; a symmetric $J$ does so only if $J = 0$. Hence $A$ is identifiable from $\{S(k)\}$ iff this equation has only the trivial solution.

**Theorem.** At a generic $(A,D,\Sigma)$ and for every $K \ge 1$, the observation map has a one-dimensional differential kernel spanned by the scaling direction, and globally $\Phi^{-1}(\Phi(\theta_0)) = \{s\theta_0 : s > 0\}$. So $(A,D,\Sigma)$ is identifiable up to a positive time rescaling: in particular the signs and ratios of the directed (antisymmetric) interactions are identifiable, and with $\Sigma$ known the parameters are fully identifiable. Structure factors at $\binom{K+1}{2} + 1$ distinct wavenumbers already suffice.

## Expansion

At $k = 0$ the Lyapunov equation alone cannot separate $A_a$ from the noise, because many drift matrices share a stationary covariance. Varying $k$ shifts the drift by $-|k|^2D$, and the family $\{S(k)\}$ is a rational function of $|k|^2$ whose coefficients encode $A$, $D$ and $\Sigma$ separately; generic injectivity is checked through the rank of the differential plus an algebraic argument for the fibre. Since each $S(k)$ is a symmetric $K\times K$ matrix, a degree count bounds the number of wavenumbers needed by $\binom{K+1}{2} + 1$. The application is inferring directed tumor-immune interactions from spatial snapshots of cell densities.

## Sources

- P. Schlicke, "Identifiability of a linear dynamical reaction-diffusion system with directed interactions from the second-order statistics of spatial snapshots" (2026), Section 2 model, Proposition 3, Proposition 4, Corollary 5, Theorem 8, Theorem 10 and Corollary 11, <https://doi.org/10.48550/arXiv.2610.07341>.
