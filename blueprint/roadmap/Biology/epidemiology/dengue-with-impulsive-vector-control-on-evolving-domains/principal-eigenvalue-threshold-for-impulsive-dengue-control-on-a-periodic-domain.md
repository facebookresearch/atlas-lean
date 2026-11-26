# Principal-eigenvalue threshold for impulsive dengue control on a periodically evolving domain

Infected humans $I_H$ and infected mosquitoes $I_V$ diffuse on a habitat $\Omega_t = \rho(t)\Omega_0$ that deforms isotropically with a $C^1$, $\tau$-periodic scaling factor $\rho$, $\rho(0) = 1$ (seasonal expansion and contraction). In fixed coordinates $y = x/\rho(t) \in \Omega_0 \subset \mathbb R^N$, with $u(y,t) = I_H(\rho(t)y,t)$ and $v(y,t) = I_V(\rho(t)y,t)$, the model is, for $t \in ((n\tau)^+, (n+1)\tau]$,

$$\partial_t u = \frac{d_H}{\rho^2(t)}\Delta u + \frac{\beta_H b}{N_H + L}\Big(\frac{b_HN_H}{m_H} - u\Big)v - \Big(\frac{N\dot\rho}{\rho} + m_H + r_H\Big)u,$$

$$\partial_t v = \frac{d_V}{\rho^2(t)}\Delta v + \frac{\beta_V b}{N_H + L}\Big(\frac{\Lambda}{m_V} - v\Big)u - \Big(\frac{N\dot\rho}{\rho} + m_V\Big)v,$$

with impulsive vector control at the times $n\tau$, $u(y,(n\tau)^+) = u(y,n\tau)$, $v(y,(n\tau)^+) = P(v(y,n\tau))$, and homogeneous Dirichlet boundary conditions. Here $b$ is the biting rate, $\beta_H,\beta_V$ transmission probabilities, $b_HN_H/m_H$ and $\Lambda/m_V$ the total human and mosquito populations, $r_H$ recovery, $L$ alternative hosts, and the term $N\dot\rho/\rho$ is dilution by domain growth. The pulse map satisfies $P \in C^1$, $P(0) = 0$, $P'(0) > 0$, $P$ nondecreasing, and $P(v)/v$ strictly decreasing with $0 < P(v)/v \le 1$ (e.g. $P(v) = cv$ or $P(v) = mv/(a+v)$).

Let $\lambda_1$ be the principal eigenvalue of the linearized periodic problem

$$\partial_t\phi_1 = \frac{d_H}{\rho^2}\Delta\phi_1 + \frac{\beta_H b}{N_H+L}\frac{b_HN_H}{m_H}\phi_2 - \Big(\frac{N\dot\rho}{\rho} + m_H + r_H\Big)\phi_1 + \lambda_1\phi_1,$$

$$\partial_t\phi_2 = \frac{d_V}{\rho^2}\Delta\phi_2 + \frac{\beta_V b}{N_H+L}\frac{\Lambda}{m_V}\phi_1 - \Big(\frac{N\dot\rho}{\rho} + m_V\Big)\phi_2 + \lambda_1\phi_2,$$

with $\phi_2(y,0^+) = P'(0)\phi_2(y,0)$, Dirichlet conditions and $\tau$-periodicity; it exists with positive eigenfunctions.

**Theorem.**

1. If $\lambda_1 \ge 0$, every solution satisfies $(u,v) \to (0,0)$ uniformly on $\bar\Omega_0$: dengue is eliminated.
2. If $\lambda_1 < 0$, the periodic problem has a unique positive $\tau$-periodic solution $(U,V)$, and every solution with nontrivial nonnegative initial data satisfies $(u(y,n\tau + t), v(y,n\tau + t)) \to (U(y,t),V(y,t))$ as $n \to \infty$: dengue persists periodically.
3. $\lambda_1$ is strictly decreasing in $P'(0)$ and in the domain $\Omega_0$: stronger pulse control (smaller $P'(0)$) and a smaller habitat raise $\lambda_1$ and favor elimination.

## Expansion

The change of variables turns the moving domain into a fixed one at the cost of a time-periodic diffusion coefficient $d/\rho^2$ and a dilution term. The linearization at $(0,0)$ is a cooperative periodic-impulsive system, so a Krein–Rutman argument on the period map gives the principal eigenvalue with positive eigenfunctions. If $\lambda_1 \ge 0$, a multiple of $e^{-\lambda_1 t}\phi$ is an upper solution and solutions decay; if $\lambda_1 < 0$, a small multiple of the eigenfunction is a lower solution, and the sublinearity of $P$ and of the incidence terms gives uniqueness and global attractivity of the positive periodic solution by monotone iteration between ordered upper and lower solutions. Monotonicity in $P'(0)$ and $\Omega_0$ follows from comparison of eigenvalue problems.

## Sources

- Han Zhang, Inkyung Ahn, Zhigui Lin, "Dengue fever model with impulsive intervention in a periodically varying environment", arXiv (2026). Section 1 (model and assumptions; Theorems 1.1–1.3), Section 2 (Theorem 2.1), Section 3 (Theorem 3.1 and monotonicity of $\lambda_1$), Section 4 (upper and lower solutions). <https://doi.org/10.48550/arXiv.2609.21205>
