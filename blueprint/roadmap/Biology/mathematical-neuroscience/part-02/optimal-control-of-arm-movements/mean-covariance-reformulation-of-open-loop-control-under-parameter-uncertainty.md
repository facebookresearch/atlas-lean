# Mean–covariance reformulation of open-loop control under parameter uncertainty

Let a limb-and-task model have state $x(t) \in \mathbb R^n$, open-loop control $u(t) \in U \subset \mathbb R^m$ and an uncertain parameter $\xi \in \mathbb R^p$ (for instance an unknown external force field) with mean $\mu$ and covariance $\Sigma$, independent of the initial state $x_0$ (mean $m_0$, covariance $P_0$). Suppose the expected cost depends on the state only through its mean $m_x = \mathbb E[x]$ and covariance $P_x$:

$$J(u) = \varphi\bigl(m_x(T), P_x(T), T\bigr) + \int_0^T \ell\bigl(m_x(t), P_x(t), u(t), t\bigr)\, dt . \tag{15}$$

1. **Affine dynamics: exact reduction.** If $\dot x = A(u,t)\,x + b(u,t) + C(u,t)\,\xi$, then $m_x, P_x$ are the first two components of the solution of

$$\dot m = A m + b + C\mu, \qquad \dot P = AP + PA^{\mathsf T} + CD^{\mathsf T} + DC^{\mathsf T}, \qquad \dot D = AD + C\Sigma,$$

with $m(0) = m_0$, $P(0) = P_0$, $D(0) = 0$, where $D = \mathbb E[(x - m)(\xi - \mu)^{\mathsf T}]$. Minimizing (15) is therefore exactly a deterministic optimal control problem in the augmented state $(m, P, D)$. It depends on the law of $\xi$ only through $\mu$ and $\Sigma$. If $x_0$ is deterministic, $P(t) = D(t)\Sigma^{-1}D(t)^{\mathsf T}$, and the state reduces to $(m, D)$ of dimension $n(p+1)$.
2. **Nonlinear dynamics: statistical linearization.** For $\dot x = f(x, u, t; \xi)$, replace the exact moments by the solution of

$$\dot m = f(m, u, t; \mu), \qquad \dot P = \mathcal A P + P\mathcal A^{\mathsf T} + \mathcal C D^{\mathsf T} + D \mathcal C^{\mathsf T}, \qquad \dot D = \mathcal A D + \mathcal C \Sigma,$$

with $\mathcal A = \partial_x f(m, u, t; \mu)$ and $\mathcal C = \partial_\xi f(m, u, t; \mu)$. If $f$ is smooth, $U$ is compact, $\xi$ takes values in a compact set and all vector fields $x \mapsto f(x,u;\xi)$ share a compact support, then on $[0,T]$ the pair $(m, P)$ converges uniformly to $(m_x, P_x)$ as $(P, D, \Sigma) \to 0$ uniformly. When $f$ is affine in $\xi$ it suffices that $(P, D) \to 0$.

## Expansion

Taking expectations of the affine equation gives the mean equation. Differentiating $\mathbb E[(x-m)(x-m)^{\mathsf T}]$ and $\mathbb E[(x-m)(\xi-\mu)^{\mathsf T}]$ gives the covariance and cross-covariance equations; no distributional assumption is needed because the dynamics are linear in $(x,\xi)$. With $P(0) = D(0) = 0$, the matrix $D\Sigma^{-1}D^{\mathsf T}$ satisfies the same linear equation and initial condition as $P$, hence equals it. In the nonlinear case the mean keeps the full nonlinear drift, and only the covariance propagation is linearized around the mean, which is accurate when spread is small. Keeping spread small is what an uncertainty-aware open-loop controller tries to achieve. In bilinear limb models, where muscle co-contraction raises joint stiffness and so enters $A(u,t)$, minimizing effort plus endpoint variance under such uncertainty makes co-contraction an optimal feedforward response to parameter uncertainty, without any feedback loop.

## Sources

- B. Berret, D. Verdel, E. Burdet, F. Jean, "Co-contraction embodies uncertainty: An optimal feedforward strategy for robust motor control", *PLoS Computational Biology* (2024), Materials and Methods ("Affine case without diffusion", Eqs. (11)–(16), Problem 2; "General nonlinear case without diffusion", Eqs. (17)–(19), Problem 3, Proposition 1), <https://doi.org/10.1371/journal.pcbi.1012598> (PMC11616891).
