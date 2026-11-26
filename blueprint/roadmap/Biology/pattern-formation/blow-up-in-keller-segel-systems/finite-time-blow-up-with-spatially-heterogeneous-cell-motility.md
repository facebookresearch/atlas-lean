# Finite-time blow-up of Keller–Segel with spatially heterogeneous cell motility

**Setting.** Let $\Omega=B_R(0)\subset\mathbb{R}^n$ with $n\ge2$, $\beta>0$ and $\alpha\ge1$. Consider

$$
u_t=\nabla\cdot(|x|^\beta\nabla u)-\nabla\cdot(u^\alpha\nabla v),\qquad 0=\Delta v-\mu+u,\quad \mu=\frac{1}{|\Omega|}\int_\Omega u,
$$

with homogeneous Neumann conditions, $\int_\Omega v=0$, and nonnegative, radially symmetric, continuous initial data $u_0\not\equiv0$ of mass $m=\int_\Omega u_0$. The motility $|x|^\beta$ degenerates at the origin, so classical solutions are sought on $\Omega_0=\bar\Omega\setminus\{0\}$.

**Theorem (local existence).** For $u_0\in C^\theta(\bar\Omega)$ there is a radially symmetric classical solution on $\Omega_0\times[0,T_0)$ for some $T_0\in(0,\infty]$, nonnegative and mass conserving. If in addition $u_0\in C^{1+\theta}(\bar\Omega)$ is radially decreasing, vanishes on $\partial\Omega$ and satisfies $|\nabla u_0(x)|\le c_0|x|^{n-1+\theta}$, then $u$ stays radially decreasing, is bounded on $\Omega_0\times[0,T]$ for every $T<T^*$, and is unique in the class with $u\in L^\infty$ and $\nabla v\in L^\infty$ on $\Omega\times(0,T)$.

**Theorem (blow-up under mass concentration).** For every $m_0\in(0,m]$ there is $r_0=r_0(m_0,m,R,\beta,\alpha)>0$ such that if $\int_{B_{r_0}(0)}u_0\ge m_0$, then no global classical solution exists with $u\in L^\infty(\Omega\times(0,T))$ and $\nabla v\in L^\infty(\Omega\times(0,T))$ for every finite $T$; that is, sufficiently concentrated data blow up in finite time.

## Expansion

In radial coordinates the mass accumulation function $w(s,t)=\int_0^{s^{1/n}}\rho^{n-1}u(\rho,t)\,d\rho$, $s\in[0,R^n]$, satisfies a scalar degenerate parabolic equation in which the motility $|x|^\beta=s^{\beta/n}$ multiplies the second-order term and the aggregation term is a power of $w_s$ times $w-\mu s/n$. A comparison principle for this scalar equation, applied to a suitably weighted moment of $w$ near the origin, yields a superlinear differential inequality whose solution cannot stay bounded for all time when enough mass sits near the origin. The degeneracy $|x|^\beta$ weakens diffusion exactly where aggregation is strongest, which is why concentration alone suffices, without a critical-mass threshold in the total mass.

## Sources

- Yashuang Zhao, Shijun Li, Shaopeng Xu, "Finite-time blow-up in a class of chemotaxis systems with spatially heterogeneous diffusion sensitivity", arXiv:2604.27561: Section 1 (system and Definition 1.1); Section 3: Theorems 3.1–3.2 (existence and uniqueness); Section 4: Theorem 4.1 (blow-up). <https://doi.org/10.48550/arXiv.2604.27561>
