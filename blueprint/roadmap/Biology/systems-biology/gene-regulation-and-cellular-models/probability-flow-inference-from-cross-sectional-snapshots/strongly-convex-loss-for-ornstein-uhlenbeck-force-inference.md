# Strongly convex loss for Ornstein-Uhlenbeck force inference

Suppose cross-sectional snapshots come from a $d$-dimensional Ornstein-Uhlenbeck process $dx = \Omega x\, dt + \sqrt{2D}\, dW$ with $\Omega$ Hurwitz (eigenvalues with negative real part), constant $D$, and $x_0 \sim \mathcal{N}(m_0, \Sigma_0)$ with $\Sigma_0$ full rank, so $x_t \sim \mathcal{N}(m_t, \Sigma_t)$ with $\Sigma_t = \sum_i \sigma_{i,t}^2 w_{i,t} w_{i,t}^{\mathsf T}$ (eigen-decomposition). A linear force $\hat f(x) = \hat\Omega x$ with an assumed constant diffusion $\hat D$ is fit by pushing samples between snapshot times $t_k = k\Delta t$, $k \le K = \lfloor T/\Delta t \rfloor$, along the probability flow ODE and minimizing

$$L_{\Delta t, K} = \sum_{i=1}^{K} \Big[ W_2^2\big(\hat p_{t_i}, p_{t_i}\big) + \lambda \Delta t \int_{t_{i-1}}^{t_i}\!\! \int \|\nabla \hat f(x)\|_F^2\, p_{t_i}(x)\, dx\, dt \Big].$$

**Theorem.** As the sample size $n \to \infty$ and $\Delta t \to 0$, $L_{\Delta t, K}/\Delta t \to \mathcal{L}$ with

$$\mathcal{L}(\hat\Omega) = \mathrm{tr}\Big( (\hat\Omega - \Omega) P (\hat\Omega - \Omega)^{\mathsf T} + \lambda T\, \hat\Omega \hat\Omega^{\mathsf T} \Big) + \int_0^T \sum_{i,p} \frac{\sigma_{i,t}^2}{(\sigma_{i,t}^2 + \sigma_{p,t}^2)^2} \Big( w_{i,t}^{\mathsf T} \big[ \sigma_{p,t}^2 (\hat\Omega - \Omega) + \sigma_{i,t}^2 (\hat\Omega^{\mathsf T} - \Omega^{\mathsf T}) + 2(\hat D - D) \big] w_{p,t} \Big)^2 dt,$$

where $P = \int_0^T m_t m_t^{\mathsf T}\, dt$. For $\lambda > 0$, $\mathcal{L}$ is strongly convex in $\hat\Omega \in \mathbb{R}^{d \times d}$ and has a unique minimizer.

## Depends on

- [Probability flow ODE and non-identifiability of force fields](probability-flow-ode-and-nonidentifiability-of-force-fields.md)

## Expansion

The first term measures how well the inferred drift moves the means, the integral measures how well it deforms the covariances, and $\lambda T \|\hat\Omega\|_F^2$ is the Jacobian penalty; the first two are convex quadratics in $\hat\Omega$ and the penalty is strongly convex, so their sum is strongly convex. With $\lambda = 0$ the quadratic form can be degenerate, which is the identifiability problem: drifts differing by directions the marginals cannot see give equal loss. For an isotropic process ($\Sigma_0 = \sigma_0^2 I$, $D = DI$, $\Omega = \Omega_s I + \Omega_a$ with $\Omega_a$ skew-symmetric) the covariance stays isotropic, so the rotational part is visible only through the mean motion encoded in $P = \sum_i \gamma_i u_i u_i^{\mathsf T}$; the minimizer is approximately $\hat\Omega \approx \Omega - Q\, \Omega_a\, Q$, where $Q$ projects onto the eigenvectors of $P$ with $\gamma_i$ below the effective penalty $\lambda K$. The regularization thus acts as a recovery threshold: non-conservative forces are recovered only along well-excited directions of the mean trajectory, and lowering $\lambda$ trades this bias for finite-sample variance (scaling like $1/(n\Delta t^2)$). Misspecifying $\hat D$ biases $\hat\Omega$, with minimal bias at $\hat D = D$, so deterministic fits ($\hat D = 0$) fail when force and noise time scales are comparable.

## Sources

- S. Maddu, V. Chardès, M. J. Shelley, "Learning stochastic processes with intrinsic noise from cross-sectional biological data", Proceedings of the National Academy of Sciences of the USA (2025), Section 2 (Eqs. 1-7: SDE, Fokker-Planck equation, probability flow ODE, identifiability condition Eq. 6, regularized loss Eq. 7), Analytical case study (OU process, Theorem 1, Eq. 8; isotropic process and approximate minimizer). <https://doi.org/10.1073/pnas.2420621122> (PMC12452938)
