# Global classical solutions of the Buruli ulcer cross-diffusion system

**Model.** *Mycobacterium ulcerans* (density $u$) invades skin tissue. It secretes the toxin mycolactone (concentration $m$), which destroys normal tissue ($v$) and turns it into necrotic matter ($n$). Bacteria move by diffusion with a tensor $\mathbb{D}_u(x)$ and by haptotaxis toward necrotic matter and normal tissue. The tactic sensitivity is damped by crowding, $a(v,n) = (1+n+v)^{-2}$. Bacteria proliferate logistically with a necrosis-dependent rate. After a parabolic scaling of a kinetic (velocity-jump) description, the nondimensional system on a bounded smooth domain $\Omega\subset\mathbb{R}^d$ reads

$$u_t = \nabla\cdot(\mathbb{D}_u\nabla u) - \nabla\cdot\big(a(v,n)\mathbb{D}_u\gamma_1 u\nabla n\big) - \nabla\cdot\big(a(v,n)\mathbb{D}_u\gamma_2 u\nabla v\big) + \frac{n}{1+n}u(1-u-v-n),$$

$$m_t = \Delta m + \frac{\delta u}{1+u} - \lambda m,\qquad v_t = -\beta_1 m v,\qquad n_t = \beta_2 m v - \gamma n,$$

with no-flux boundary conditions. Here $\gamma_1$ and $\gamma_2$ carry the turning-rate weight from the kinetic level.

**Assumptions.** (A1) $\mathbb{D}_u \in \big(C^{2,\rho}(\Omega)\cap C(\overline\Omega)\big)^{d\times d}$ for some $\rho\in(0,1)$, and it is uniformly elliptic: $\xi^{\top}\mathbb{D}_u(x)\xi \ge \Lambda|\xi|^2$. The initial data are nonnegative, with $u_0 \in W^{1,\infty}(\Omega)$ and $m_0, v_0, n_0 \in W^{2,\infty}(\Omega)$ satisfying the boundary compatibility conditions.

**Theorem.** Under (A1), the system has a nonnegative classical solution $(u, m, v, n)$ that exists globally in time. Along the way:

- local classical solutions exist, and either $T_{\max} = \infty$ or $\|u\|_{L^\infty} + \|m\|_{W^{1,\infty}} + \|v\|_{W^{1,\infty}} + \|n\|_{W^{1,\infty}}$ is unbounded as $t\uparrow T_{\max}$;
- $\|m\|_{L^\infty} \le \|m_0\|_{L^\infty} + \delta/\lambda$ and $\|\nabla m\|_{L^\infty} \le C(\|\nabla m_0\|_{L^\infty}+1)$;
- for every $p > 1$, $\|u(t)\|_{L^p}$ stays bounded on $(0, T_{\max})$.

A global existence result along the same lines holds for the second model, derived from a lattice (biased random walk) approach, in which the diffusion and tactic coefficients depend nonlinearly on $(u, v, n)$.

## Expansion

The proof follows the strategy for chemotaxis–haptotaxis systems. Local existence comes from a fixed-point argument on a bounded convex set of bacterial densities. The ODEs for $v$ and $n$ are solved explicitly in terms of $m$: $v = v_0 e^{-\beta_1\int_0^t m}$ is bounded by $v_0$, and $n$ is controlled by $\int m$. The bound $\delta u/(1+u) \le \delta$ gives an $L^\infty$ bound on $m$ from the Neumann heat semigroup, and smoothing estimates give $\nabla m$, hence $\nabla v$ and $\nabla n$, in $L^\infty$. The saturating factor $a(v,n)$ and the logistic damping $-u^2 n/(1+n)$ then allow $L^p$ energy estimates for $u$ for all $p$. A Moser iteration upgrades them to an $L^\infty$ bound on $u$ on every finite time interval, which together with the dichotomy rules out blow-up.

## Sources

- S. Chettiparambil Mohanan, C. Surulescu and N. N. Pelen, "Mathematical modeling of Buruli ulcer spread", arXiv:2503.14230 (2025), Section 2 (modeling), assumption (A1), Lemmas 3.1, 3.3 and 3.6, and Theorem 3.8, <https://doi.org/10.48550/arXiv.2503.14230>.
