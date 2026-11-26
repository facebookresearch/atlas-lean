# Graphon limit of a stochastic patch occupancy metacommunity

**Model.** Let $\Omega\subset\mathbb R^d$ be a habitat with site density $\mu$. There are $K$ patches at positions $x_1,\dots,x_K\in\Omega$, each in a state $w_k(t)\in\{0,1,\dots,S\}$ (empty or occupied by species $i$). A patch in state $i\ge1$ at $x$ becomes empty at rate $\tau_i(x)$; a patch at $x$ in state $j$ is taken over by species $i$ at rate $\frac1K\sum_{\ell}c_{i,j}(x,x_\ell)\mathbf 1\{w_\ell=i\}$. The empirical measure is $\eta^K_t=\frac1K\sum_k\delta_{(x_k,w_k(t))}$ on $E=\Omega\times\{0,\dots,S\}$.

**Theorem 2.4 (law of large numbers).** Under bounded jump rates and convergence of the initial empirical measures to $\mu(x)dx\sum_iu^0_i(x)\delta_i$, the processes $\eta^K$ converge in probability in $\mathbb D(\mathbb R_+,\mathcal M_1(E))$ to the deterministic measure-valued process
$$\zeta_t(dx,dw)=\mu(x)\,dx\sum_{i=0}^Su_i(t,x)\,\delta_i(dw),$$
where $\sum_iu_i=1$, $u_i\in[0,1]$, and for $i=1,\dots,S$
$$\partial_tu_i(t,x)=-\tau_i(x)u_i+\sum_{j=0}^Su_j(t,x)\int_\Omega u_i(t,y)c_{i,j}(x,y)\mu(y)\,dy-u_i(t,x)\sum_{j=1}^S\int_\Omega u_j(t,y)c_{j,i}(x,y)\mu(y)\,dy .$$
The limit system has a unique solution (Propositions A.4–A.5).

**Two competitors for empty sites.** With $S=2$, $\mu\equiv1$, colonization only of empty patches ($c_{1,0}=c$, $c_{2,0}=\gamma$, all other $c_{i,j}=0$), extinction rates $\tau,\sigma$ and occupancies $u=u_1$, $v=u_2$:
$$\partial_tu=-\tau(x)u+(1-u-v)\int_\Omega u(t,y)c(x,y)\,dy,\qquad \partial_tv=-\sigma(x)v+(1-u-v)\int_\Omega v(t,y)\gamma(x,y)\,dy,$$
with $u_0+v_0\le1$, and the theorem gives existence and uniqueness of solutions with $0\le u+v\le1$.

## Depends on

- [Levins metapopulation on a patch network](../levins-metapopulation-on-a-patch-network/README.md)

## Expansion

The empirical measure solves a measure-valued SDE driven by Poisson point processes (Proposition 2.2). Bounded rates give C-tightness in the Skorokhod space (Proposition A.2); any limit point solves the measure-valued integral equation (Proposition A.3); and two solutions with the same initial condition coincide in total variation (Proposition A.4). Uniqueness of the limit therefore yields convergence of the whole sequence, and the convergence itself proves existence for the integro-differential system. With one site per location this is the continuum (graphon) version of Levins' $\dot p=cp(1-p)-ep$.

## Sources

- M. Costa, M. Kubasch, N. Loeuille, "Metacommunity persistence on spatially heterogeneous landscapes", arXiv preprint (2026), Proposition 2.2, Theorem 2.4 and Propositions A.2–A.5, <https://doi.org/10.48550/arXiv.2607.11291>.
