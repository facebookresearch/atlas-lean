# Global threshold dynamics of the multi-host multi-vector model

**Setting.** Consider the multi-host, multi-stage, multi-vector $SEI^nR$–$SI$ model with $m$ host species, $n$ infectious stages per host and $p$ vector species, and its basic reproduction number $\mathcal R_0(m,n,p)$ ([basic reproduction number of the multi-host multi-vector model](basic-reproduction-number-of-the-multi-host-multi-vector-model.md)). All parameters are positive except the biting and infectiousness matrices $A$, $B^\diamond$, $B_l$, which are nonnegative. Encode the host-vector transmission network by the block matrix

$$
\mathcal N = \begin{pmatrix} \mathbf 0 & A\circ B^\diamond \\ \sum_{l=1}^n (A\circ B_l)^{T} & \mathbf 0 \end{pmatrix}.
$$

An equilibrium is *strongly endemic* if every infectious stage of every host species and every vector species is strictly positive: $I^*_{l,i}>0$ and $I^*_{v,j}>0$ for all $l,i,j$.

**Theorem.**

1. If $\mathcal R_0^2(m,n,p)<1$, the disease-free equilibrium is globally asymptotically stable on the nonnegative orthant. No irreducibility assumption on $\mathcal N$ is needed.
2. If $\mathcal R_0^2(m,n,p)>1$ and $\mathcal N$ is irreducible, there is a unique strongly endemic equilibrium.
3. Whenever the strongly endemic equilibrium exists, it is globally asymptotically stable (on the region where the infection is present).

So for an irreducible host-vector configuration the dynamics are a sharp dichotomy: either the pathogen dies out in all hosts and vectors, or it persists at a unique positive level in every host stage and every vector species.

## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Expansion

*Extinction.* Bounding $\mathbf S_h\le\mathbf N_h$ and $\mathbf S_v\le\mathbf N_v$ shows that the infected vector $(\mathbf E,\mathbf I_1,\dots,\mathbf I_n,\mathbf I_v)$ satisfies $\dot{\mathbf y}\le(F+V)\mathbf y$, where $F\ge 0$ and $V$ is Metzler. Since $\rho(-FV^{-1})<1$ iff the stability modulus of $F+V$ is negative, the comparison theorem drives all infected classes to zero, and the susceptibles converge to their disease-free values. Together with local stability this gives global stability without the usual left-eigenvector Lyapunov function, which is why irreducibility is not required.

*Endemic.* The equilibrium relations reduce to a fixed-point problem whose positive solution exists and is unique when $\mathcal R_0^2>1$ and $\mathcal N$ is irreducible. Global stability uses a Volterra-type Lyapunov function $\sum_i v_i\mathcal V_i$. Each $\mathcal V_i$ sums the terms $\int_{z^*}^{z}(1 - z^*/x)\,dx$ over the host compartments $S_i,E_i,I_{k,i}$ (with stage weights $c_{k,i}$, $c_{1,i} = (\nu_i+\mu_i)/\nu_i$) and over the vector compartments, weighted by $w_{ij} = a_{ij}\beta^\diamond_{ij}S_i^*/\bigl(N_i(\mu_{v,j}+\delta_{v,j})\bigr)$. The weights $v_i>0$ are a positive kernel vector of a Laplacian-type linear system $\bar B v = 0$ built from the endemic fluxes, which balances the cross terms; the remaining terms are nonpositive by the arithmetic–geometric mean inequality, so $\dot{\mathcal V}\le 0$, and LaSalle's invariance principle concludes.

## Sources

- Derdei Mahamat Bichara, "Global analysis of multi-host and multi-vector epidemic models", Journal of Mathematical Analysis and Applications 475 (2019), 1532–1553, <https://doi.org/10.1016/j.jmaa.2019.03.030>. Published version of arXiv:1807.02918, cited next; locators there refer to the arXiv version.
- Derdei Bichara, "Global Analysis of Multi-Host and Multi-Vector Epidemic Models", arXiv 2018: Section 3, Theorem 3.1, Theorem 3.2, Theorem 3.3 and the remark following Theorem 3.1. <https://doi.org/10.48550/arXiv.1807.02918>
