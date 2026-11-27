# Equilibria and global convergence of a fixed-host mobile-vector SEI–SI model

**Model.** On a bounded $C^1$ domain $\Omega\subset\mathbb R^d$, fixed hosts with susceptible, exposed and infectious densities $S_h,E_h,I_h$ and mobile vectors with susceptible and infectious densities $S_v,I_v$ satisfy

$$
\begin{aligned}
\partial_tS_h&=-\beta_v(x)S_hI_v, & \partial_tE_h&=\beta_v(x)S_hI_v-\varepsilon E_h, & \partial_tI_h&=\varepsilon E_h,\\
\partial_tS_v&=\Delta\bigl(D(x)S_v\bigr)-\beta_h(x)S_vI_h, & \partial_tI_v&=\Delta\bigl(D(x)I_v\bigr)+\beta_h(x)S_vI_h, &&
\end{aligned}
$$

with zero-flux boundary conditions $\partial_n(DS_v)=\partial_n(DI_v)=0$ on $\partial\Omega$, a positive motility $D(x)$, positive transmission rates $\beta_v,\beta_h$ and incubation rate $\varepsilon>0$. Host density is conserved pointwise and vector mass globally:

$$
S_h+E_h+I_h\equiv N(x),\qquad \int_\Omega\bigl(S_v+I_v\bigr)\,dx\equiv C^* .
$$

Let $|\Omega|_\mu=\int_\Omega dx/D(x)$.

**Proposition (Proposition 2.1).** Let $N\in C(\bar\Omega)$ be positive and $C^*>0$. The only nonnegative stationary solutions satisfying the conservation laws and the boundary condition are

$$
\Bigl(N(x),0,0,\frac{C^*}{|\Omega|_\mu D(x)},0\Bigr)\quad\text{(disease-free)}\qquad\text{and}\qquad\Bigl(0,0,N(x),0,\frac{C^*}{|\Omega|_\mu D(x)}\Bigr)\quad\text{(fully infected)} .
$$

The disease-free state is globally unstable and the fully infected state is globally stable: any introduction of infection eventually infects every host, and all vectors become infectious, distributed with density inversely proportional to their motility.

**Proposition (exponential convergence, Proposition 2.2).** Write $s_v=DS_v$ and $i_v=DI_v$. For smooth nonnegative initial data that carry some infection, $E_h^0+I_h^0\not\equiv0$ or $I_v^0\not\equiv0$, there are constants $C,\lambda>0$ with $\|S_h(t)\|_\infty,\|E_h(t)\|_\infty\le Ce^{-\lambda t}$, $\|s_v(t)\|_\infty\le Ce^{-\lambda t}$, $\|I_h(t)-N\|_\infty\le Ce^{-\lambda t}$, and $\|i_v(t)-\langle i_v(t)\rangle\|_{L^2(\Omega)}\le Ce^{-\lambda t}$, where $\langle\cdot\rangle$ is the spatial mean. The infection hypothesis is needed: disease-free data $(N,0,0,S_v^0,0)$ give $S_h\equiv N$ for all time. The source states the proposition for all smooth data; its proof uses that $i_v$ tends to the total vector density, which holds only when infection is present.

## Expansion

Stationary vector densities $u$ satisfy $\Delta(Du)=0$ with $\partial_n(Du)=0$, so $Du$ is constant and $u=c/D$; at equilibrium $\beta_vS_hI_v=0$ and $\beta_hS_vI_h=0$, which with $E_h=0$ and the conservation laws leaves only the two listed states, the constant fixed by $\int u=C^*$. Instability of the disease-free state and stability of the infected one follow because $I_h$ is nondecreasing and the vector total $a=S_v+I_v$ solves a pure diffusion problem, so $D a$ converges to its mean; the infection equation reduces to a scalar nonlocal reaction–diffusion equation $\partial_ti_v-D\Delta i_v=(a-i_v)f(t,x,i_v)$ with $f\ge0$ eventually bounded below, forcing $i_v\to a$. The model has no host or vector demography, so the long-term question is the transient phase, which the source studies by global sensitivity analysis.

## Sources

- O. Martin, Y. Fernandez-Diclo, J. Coville, C. Bruchou and S. Soubeyrand, "Equilibrium and sensitivity analysis of a spatio-temporal host-vector epidemic model", arXiv:2002.07542 (2020), Section 2 (system $\mathcal M_1$, invariance conditions, Propositions 2.1–2.2) and the appendix proofs, <https://doi.org/10.48550/arXiv.2002.07542>.
