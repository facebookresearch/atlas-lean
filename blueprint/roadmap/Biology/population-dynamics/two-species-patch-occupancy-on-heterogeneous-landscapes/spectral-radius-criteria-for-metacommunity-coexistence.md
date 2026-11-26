# Spectral-radius criteria for metacommunity coexistence

**Setting.** On a compact habitat $\Omega$, two species compete for empty sites:
$$\partial_tu=-\tau(x)u+(1-u-v)\int_\Omega c(x,y)u(t,y)\,dy,\qquad \partial_tv=-\sigma(x)v+(1-u-v)\int_\Omega\gamma(x,y)v(t,y)\,dy,$$
with continuous positive extinction rates $\tau,\sigma$ and colonization kernels $c,\gamma$, and $u_0+v_0\le1$. Define the first-generation operators and the occupancy scaling on $L^\infty(\Omega,\mathbb R_+)$:
$$\mathcal T_u g(x)=\int_\Omega\frac{c(x,y)g(y)}{\tau(y)}dy,\qquad \mathcal T_vg(x)=\int_\Omega\frac{\gamma(x,y)g(y)}{\sigma(y)}dy,\qquad \mathcal S_pg(x)=(1-p(x))g(x),$$
and let $r(\cdot)$ denote spectral radius. If $r(\mathcal T_u)>1$, species $u$ alone has a unique positive equilibrium $\bar u$ that attracts every nonzero initial condition (the single-species threshold theorem, Theorem 2.6, from Delmas–Dronnier–Zitt); similarly $\bar v$.

**Theorems 2.7–2.9 and Proposition 2.10.**
1. (Complete extinction) If $r(\mathcal T_u)\le1$ and $r(\mathcal T_v)\le1$, then $\|u(t)\|_\infty,\|v(t)\|_\infty\to0$.
2. (Single-species extinction) If $r(\mathcal T_u)\le1<r(\mathcal T_v)$, then $\|u(t)\|_\infty\to0$ and $v(t,x)\to\bar v(x)$ for every $x$.
3. (Uniform strong persistence) If $r(\mathcal T_u)>1$, $r(\mathcal T_v)>1$, $r(\mathcal T_u\circ\mathcal S_{\bar v})>1$ and $r(\mathcal T_v\circ\mathcal S_{\bar u})>1$, there is $\epsilon>0$ with $\liminf_tu>\epsilon$ and $\liminf_tv>\epsilon$ for all admissible initial conditions.
4. (Bistability) If $r(\mathcal T_u)>1$, $r(\mathcal T_v)>1$ but $r(\mathcal T_u\circ\mathcal S_{\bar v})\le1$ and $r(\mathcal T_v\circ\mathcal S_{\bar u})\le1$, both $(\bar u,0)$ and $(0,\bar v)$ are locally stable.

**Theorems 3.3–3.4 (patch version).** For finitely many patch types the same dichotomies hold with the spectral bounds $s(M_u(0)),s(M_v(0)),s(M_u(\bar{\mathbf v})),s(M_v(\bar{\mathbf u}))$ of the linearized colonization–extinction matrices in place of $r(\cdot)-1$, and mutual invasibility also yields a positive coexistence equilibrium $(\mathbf u^*,\mathbf v^*)$ with $\mathbf u^*\le\bar{\mathbf u}$, $\mathbf v^*\le\bar{\mathbf v}$.

## Depends on

- [Graphon limit of a stochastic patch occupancy metacommunity](graphon-limit-of-a-stochastic-patch-occupancy-metacommunity.md)

## Expansion

$r(\mathcal T_u)$ is the habitat-wide basic reproduction number of species $u$: the expected number of patches colonized from one occupied patch during its lifetime, averaged along the principal eigenfunction. Each species is a monotone single-species system dominated by its own equation with $v\equiv0$, which gives the extinction statements by comparison with the threshold theorem. Invasion of the resident equilibrium $\bar v$ is governed by the linearization $\partial_tu\approx-\tau u+(1-\bar v)\int cu$, whose growth sign is that of $r(\mathcal T_u\circ\mathcal S_{\bar v})-1$; mutual invasibility plus dissipativity gives uniform persistence by acyclicity of the boundary dynamics. The patch version reduces to the Lajmanovich–Yorke multigroup theorem (Theorem 3.1) for each species alone.

## Sources

- M. Costa, M. Kubasch, N. Loeuille, "Metacommunity persistence on spatially heterogeneous landscapes", arXiv preprint (2026), Theorems 2.6–2.9, Proposition 2.10, Theorems 3.1, 3.3 and 3.4, <https://doi.org/10.48550/arXiv.2607.11291>.
