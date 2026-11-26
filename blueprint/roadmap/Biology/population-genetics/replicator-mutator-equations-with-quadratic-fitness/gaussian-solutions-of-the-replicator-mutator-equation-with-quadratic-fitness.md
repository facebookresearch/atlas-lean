# Gaussian solutions of the replicator–mutator equation with quadratic fitness

**Model.** A population density $q(t, x)$ over a continuous trait $x \in \mathbb{R}^d$ (not necessarily normalized) evolves by the continuous-time, continuous-trait replicator–mutator equation

$$\partial_t q(t,x) = -\nabla\cdot\big(q(t,x)\,Gx\big) + \tfrac12 \nabla\cdot\big(\Sigma \nabla q(t,x)\big) + q(t,x)\,\pi_{q_t}(x),$$

where mutation is an Ornstein–Uhlenbeck diffusion with drift matrix $G$ and symmetric positive definite covariance $\Sigma$ ($G = 0$ is a random-walk mutation kernel). The fitness is frequency dependent,

$$\pi_{q_t}(x) = \frac{\int f(x,z)\, q_t(z)\,dz}{\int q_t(z)\,dz}, \quad f(x,z) = -\tfrac12\|Ax - y(t)\|_\Gamma^2 - \tfrac12\|Az - y(t)\|_\Gamma^2 + s\,\langle Ax - y(t), Az - y(t)\rangle_\Gamma + K,$$

with $A \in \mathbb{R}^{k \times d}$, a possibly moving optimum $y(t) \in \mathbb{R}^k$, a positive definite $\Gamma$, $\|v\|_\Gamma^2 = v^{\mathsf T}\Gamma^{-1}v$, an interaction parameter $s \le 1$ and a constant $K$. Write $Q = A^{\mathsf T}\Gamma^{-1}A$.

**Theorem.**
1. *(Gaussian closure.)* If $q_0 = P_0\,\mathcal{N}(m_0, C_0)$, then $q_t = P(t)\,\mathcal{N}(m(t), C(t))$ for all $t \ge 0$, with

$$\dot m = Gm - (1 - s)\,C A^{\mathsf T}\Gamma^{-1}(Am - y(t)),\qquad \dot C = GC + CG^{\mathsf T} + \Sigma - CQC,$$

$$\dot P = P\big(K - (1-s)\|Am - y(t)\|_\Gamma^2 - \mathrm{tr}(QC)\big).$$

For $s = 0$ the equations for $(m, C)$ are exactly the Kalman–Bucy filter for a hidden state with dynamics $G$, noise $\Sigma$ and observations $Ax$ of the optimum $y(t)$ with noise covariance $\Gamma$.
2. *(Pure replication: covariance.)* If $G = 0$ and $\Sigma = 0$, then $C(t) = M(t)\,C_0$ with $M(t) = (I + tC_0 Q)^{-1}$, and $M(t)$ converges to the $C_0$-orthogonal projection onto $\ker A$; in particular $C(t) \to 0$ when $C_0 Q$ is invertible.
3. *(Pure replication: mean.)* For a constant optimum $y$,

$$m(t) = M^{1-s}(t)\,m_0 + \big[I - M^{1-s}(t)\big]\,Q^{+}A^{\mathsf T}\Gamma^{-1}y,$$

and if $s < 1$ and $C_0 \succ 0$, $m(t)$ converges to $\arg\min\{\|u - m_0\|_{C_0}^2 : u \in \arg\min_v \|Av - y\|_\Gamma^2\}$. For $s = 0$ and a moving optimum the same formula holds with $y$ replaced by the running average $\frac1t\int_0^t y(u)\,du$.

## Expansion

Quadratic fitness acts on a Gaussian density like a Gaussian likelihood acts on a Gaussian prior, so the Gaussian family is invariant and selection performs a Bayesian update at rate one; mutation adds the diffusion $\Sigma$ to the covariance, giving a matrix Riccati equation in which selection shrinks and mutation inflates trait variance. Without mutation the population concentrates at the fitness optimum closest to its starting mean in the $C_0$ geometry, a Tikhonov-regularized least-squares solution, and it averages a moving optimum over its whole history. With mutation the covariance reaches the Riccati equilibrium, which quantifies lag behind a moving optimum and effects such as survival of the flattest.

## Sources

- S. Pathiraja, P. Wacker, "Mathematical description of continuous time and space replicator-mutator equations for quadratic fitness", arXiv:2412.08178 (2024), Section 3 model equations, Lemma 3.4, Lemma 3.7, Lemmas 3.9–3.10 and Lemma 3.14, <https://doi.org/10.48550/arXiv.2412.08178>.
