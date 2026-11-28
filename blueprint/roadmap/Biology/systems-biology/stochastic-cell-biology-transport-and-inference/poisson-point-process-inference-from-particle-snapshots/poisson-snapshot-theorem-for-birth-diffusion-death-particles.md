# Poisson snapshot theorem for birth–diffusion–death particles

Particles are born at the points $0 > T_1 > T_2 > \dots$ of a stationary Poisson process of rate $\lambda$ on the negative half-line, at i.i.d. initial positions with density $f$ on an open domain $\Omega \subset \mathbb{R}^d$ with compact closure whose boundary points are all regular. Each particle then follows, independently and in nondimensional units, the diffusion

$$ dX_i(t) = \alpha(X_i(t))\, dt + \sqrt{2}\, dB_i(t), \qquad t > T_i, \qquad X_i(T_i) = \xi_i , $$

with generator $\mathcal{L}h = \alpha\cdot\nabla h + \Delta h$, switches from active to inactive at rate $\mu$ (degradation), and is lost forever when it first exits $\Omega$. Let $N(A)$ count the particles that are still active and inside $\Omega$ at the snapshot time $0$ and lie in $A \subseteq \Omega$.

**Theorem.** $N$ is a Poisson spatial point process on $\Omega$ whose intensity $u$ solves the boundary value problem

$$ \mathcal{L}^* u - \mu u = -\lambda f \ \text{ in } \Omega, \qquad u = 0 \ \text{ on } \partial\Omega, \qquad \mathcal{L}^* u = -\nabla\cdot(\alpha u) + \Delta u . $$

That is, for disjoint Borel sets $A_1, \dots, A_K$ the counts $N(A_k)$ are independent with $N(A_k) \sim \mathrm{Pois}\big(\int_{A_k} u(x)\,dx\big)$.

In one dimension with $\Omega = (0,L)$, no drift and a point source at $z$, the intensity is an explicit combination of hyperbolic functions,.

## Expansion

Each particle born at time $T_i < 0$ contributes to the snapshot independently, and the marking theorem for Poisson processes shows that the surviving active particles form a Poisson process whose intensity at $x$ is $\lambda\int_0^\infty \int_\Omega f(y)\, e^{-\mu s} p^{\Omega}_s(y,x)\,dy\,ds$, with $p^\Omega$ the transition density of the diffusion killed at $\partial\Omega$. Integrating the killed forward equation $\partial_s p = \mathcal{L}^* p$ in $s$ shows that this resolvent solves the stated boundary value problem with homogeneous Dirichlet data. The theorem is the bridge between individual stochastic paths and a population-level elliptic PDE, without requiring enough particles to approximate a continuum density.

## Sources

- Christopher E. Miles, Scott A. McKinley, Fangyuan Ding, Richard B. Lehoucq, "Inferring Stochastic Rates from Heterogeneous Snapshots of Particle Positions", Bulletin of Mathematical Biology 86 (2024), 74, <https://doi.org/10.1007/s11538-024-01301-4>. Published version of arXiv:2311.04880, cited next; locators there refer to the arXiv version.
- C. E. Miles, S. A. McKinley, F. Ding, R. B. Lehoucq, "Inferring stochastic rates from heterogeneous snapshots of particle positions", arXiv:2311.04880 (2023), Section 2.2 (stochastic model; Theorem 2.1 and Remark 2.2), Section 3 (one-dimensional analytical solution) and Section 4.1 (proof of Theorem 2.1). <https://doi.org/10.48550/arXiv.2311.04880>
