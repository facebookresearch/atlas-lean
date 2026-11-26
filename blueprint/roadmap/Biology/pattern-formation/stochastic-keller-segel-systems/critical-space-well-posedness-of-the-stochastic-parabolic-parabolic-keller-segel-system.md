# Critical-space well-posedness of the stochastic parabolic-parabolic Keller-Segel system

**Setting.** On the torus $\mathbb{T}^d$ with $d \ge 3$, consider the stochastic Keller-Segel system for a cell density $u$ and a chemoattractant $v$,

$$
\begin{aligned}
\mathrm{d}u &= \big(\Delta u - \operatorname{div}(u \nabla v)\big)\,\mathrm{d}t + \sum_{n \ge 1} g^1_n(u, v, \nabla v)\,\mathrm{d}W^1_n,\\
\mathrm{d}v &= (\Delta v + u - v)\,\mathrm{d}t + \sum_{n \ge 1} g^2_n(v)\,\mathrm{d}W^2_n,
\end{aligned}
$$

driven by independent families of standard Brownian motions $(W^1_n)$, $(W^2_n)$, with noise coefficients satisfying Lipschitz and growth bounds of lower order than the chemotactic term. The heat scaling $u_\lambda(t,x) = \lambda u(\lambda t, \lambda^{1/2} x)$, $v_\lambda(t,x) = v(\lambda t, \lambda^{1/2}x)$ leaves the deterministic part invariant, and the Besov spaces

$$
B^{d/q - 2}_{q,p}(\mathbb{T}^d) \times B^{d/q_v}_{q_v,p}(\mathbb{T}^d)
$$

are invariant under the induced scaling of the initial data; these are the scaling-critical spaces.

**Parameters.** Work in $X_0 = H^{s,q} \times H^{s_v,q_v}$, $X_1 = H^{2+s,q} \times H^{2+s_v,q_v}$ with time weight $w_\kappa(t) = t^\kappa$, where either $q, q_v \in [2, \infty)$, $p \in (2,\infty)$, $\kappa \in [0, p/2 - 1)$, or $q = q_v = p = 2$, $\kappa = 0$, and

$$
s \in (-2,-1],\quad s_v \in (-1,1],\quad s_v + 2 - \tfrac{2(1+\kappa)}{p} = \tfrac{d}{q_v},\quad s + 2 - \tfrac{d}{q} = s_v - \tfrac{d}{q_v},\quad s \ge -\tfrac{d}{q},\ s_v \ge -\tfrac{d}{q_v},\quad s_v \le s + 2 .
$$

These constraints are compatible only for $d \ge 3$; for $d = 3$ they force $(p, \kappa, s, q, s_v, q_v) = (2, 0, -3/2, 2, 1/2, 2)$, i.e. data in $H^{-1/2} \times H^{3/2}$.

**Theorem (local well-posedness).** For every $\mathfrak{F}_0$-measurable initial datum $(u_0, v_0)$ with values in $B^{d/q-2}_{q,p} \times B^{d/q_v}_{q_v,p}$ there is an $L^p_\kappa$-maximal strong solution $((u,v), \sigma)$ with $\sigma > 0$ almost surely, and it is unique: two maximal solutions with the same initial data have the same lifetime and coincide up to it. For $p \ne 2$ the solution has the extra regularity $u \in H^{\theta,p}((0,\sigma_n), w_\kappa; H^{2(1-\theta)+s,q})$, $v \in H^{\theta,p}((0,\sigma_n), w_\kappa; H^{2(1-\theta)+s_v,q_v})$ for every $\theta \in [0, 1/2)$ along a localizing sequence $\sigma_n \uparrow \sigma$.

**Theorem (small data gives long existence with high probability).** If in addition the noise vanishes suitably at zero, then for every $T < \infty$ there is $C_T > 0$ such that for every $\varepsilon \in (0,1)$,

$$
\mathbb{E}\,\|(u_0, v_0)\|^p_{B^{d/q-2}_{q,p} \times B^{d/q_v}_{q_v,p}} \le C_T\,\varepsilon \quad\Longrightarrow\quad \mathbb{P}(\sigma \ge T) \ge 1 - \varepsilon .
$$

## Expansion

Write the system as a semilinear stochastic evolution equation $\mathrm{d}U + AU\,\mathrm{d}t = F(U)\,\mathrm{d}t + B(U)\,\mathrm{d}W$ with the triangular linear part $-A = \begin{pmatrix} \Delta & 0 \\ \mathrm{Id} & \Delta - \mathrm{Id}\end{pmatrix}$, which has stochastic maximal $L^p_\kappa$-regularity on $X_0$. The trace space of this regularity class is the real interpolation space $B^{s + 2 - 2(1+\kappa)/p}_{q,p} \times B^{s_v + 2 - 2(1+\kappa)/p}_{q_v,p}$, and the parameter equalities make it coincide in leading order with the critical Besov space. Paraproduct and Sobolev embedding estimates show that the chemotactic nonlinearity $\operatorname{div}(u \nabla v)$ is bilinear-bounded from intermediate spaces $H^{\gamma,q} \times H^{\gamma_v,q_v}$ into $H^{s,q}$ with exactly the critical exponent, and that the noise coefficients are Lipschitz into $H^{1+s,q} \times H^{1+s_v,q_v}$. The abstract critical local well-posedness theory for quasilinear stochastic evolution equations then gives the maximal unique solution. For small data, a stopped fixed-point argument with smallness in expectation controls the solution up to time $T$ on an event of probability at least $1 - \varepsilon$.

## Sources

- Jae-Hwan Choi, Ankit Kumar, Andrea Pitrone and Shyam Popat, "The stochastic Keller--Segel system in critical spaces", arXiv (2026), Section 3 (scaling-critical spaces and parameter conditions), Theorem 3.4 (local well-posedness), Theorem 3.5 (small data and long existence), Theorem 4.2 and Lemma 4.3, <https://doi.org/10.48550/arXiv.2607.27472>.
