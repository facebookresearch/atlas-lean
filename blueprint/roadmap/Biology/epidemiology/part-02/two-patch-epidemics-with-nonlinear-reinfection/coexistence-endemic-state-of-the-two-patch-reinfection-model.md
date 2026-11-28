# Coexistence endemic state of the two-patch reinfection model

For patches $j\in\{u,r\}$ (urban, rural) let $S_j$, $I_j$, $\widetilde S_j$ be susceptible, infected and post-recovery susceptible numbers, $N_j=S_j+I_j+\widetilde S_j$, with equal birth and death rate $\mu_j$, infection rate $\beta_j$, recovery rate $\gamma_j$, reinfection rate $\rho_j$, and constant movement fractions $\delta_{ur}$ (urban to rural) and $\delta_{ru}$ (rural to urban). The urban equations are

$$\begin{aligned}\dot S_u&=\mu_uN_u-\beta_u\frac{I_u}{N_u}S_u-\mu_uS_u+\delta_{ru}S_r-\delta_{ur}S_u,\\ \dot I_u&=\beta_u\frac{I_u}{N_u}S_u-(\mu_u+\gamma_u)I_u+\rho_u\frac{I_u}{N_u}\widetilde S_u+\delta_{ru}I_r-\delta_{ur}I_u,\\ \dot{\widetilde S}_u&=\gamma_uI_u-\rho_u\frac{I_u}{N_u}\widetilde S_u-\mu_u\widetilde S_u+\delta_{ru}\widetilde S_r-\delta_{ur}\widetilde S_u,\end{aligned}$$

and the rural equations are obtained by swapping $u\leftrightarrow r$. Total patch sizes obey the linear system $\dot N_u=-\delta_{ur}N_u+\delta_{ru}N_r=-\dot N_r$. The local basic reproduction numbers are

$$\mathcal R_{0u}=\frac{\beta_u}{\gamma_u+\mu_u},\qquad \mathcal R_{0r}=\frac{\beta_r}{\gamma_r+\mu_r}.$$

**Theorem (endemic state in both patches).** If

$$\mathcal R_{0u}>1+\frac{\delta_{ur}}{\mu_u+\gamma_u}\quad\text{and}\quad \mathcal R_{0r}>1+\frac{\delta_{ru}}{\mu_r+\gamma_r},$$

then the model has at least one steady state with $I_u^*>0$ and $I_r^*>0$. Numerically there can be several such states (the steady-state system reduces to a degree-9 polynomial, and for suitable parameters all nine roots are feasible, four of them stable), reflecting the backward bifurcation that nonlinear reinfection causes in each patch.

**Corner-cutting Poincaré–Miranda lemma.** Let $F=(F_1,F_2):[0,1]^2\to\mathbb R^2$ be continuous with $F(0,0)=0$, $F_1(x,0)>0$ for $x\in(0,1]$, $F_1(x,1)<0$ for $x\in[0,1]$, $F_2(0,y)>0$ for $y\in(0,1]$, $F_2(1,y)<0$ for $y\in[0,1]$, and suppose $\partial F_1/\partial y$, $\partial F_2/\partial x$ are right-continuous at the origin with positive values there. Then $F$ has a zero in $(0,1)^2$.

## Expansion

At equilibrium $\delta_{ur}N_u=\delta_{ru}N_r$. Fix trial prevalences $(B_u,B_r)\in[0,1]^2$ in place of $I_j/N_j$ in the incidence terms; the steady-state equations become linear and give explicit fractions $i_u(B_u,B_r)$, $i_r(B_u,B_r)$. A true steady state is a zero of $G=(i_u-B_u,\,i_r-B_r)$. On the far faces $G_1(1,B_r)<0$ and $G_2(B_u,1)<0$; on the near faces $G_1(0,B_r)=i_u(0,B_r)\ge0$, vanishing only at the origin, which is the disease-free state. The hypotheses give $\partial G_1/\partial B_u(0,0)>0$ and $\partial G_2/\partial B_r(0,0)>0$, so the lemma, after shrinking the box away from the origin, applies the classical Poincaré–Miranda theorem (the $n$-dimensional Bolzano theorem) and yields a zero with both prevalences positive.

## Depends on

- [Disease-free stability of the two-patch reinfection model](disease-free-stability-of-the-two-patch-reinfection-model.md)

## Sources

- J. G. Calvo, A. Hernández, M. A. Porter and F. Sanchez, *A two-patch epidemic model with nonlinear reinfection*, arXiv:1907.08887 (2019), Theorem 3.5, Proposition 3.6, Lemma 3.7, Remark 3.8 and Example 4.7. <https://doi.org/10.48550/arXiv.1907.08887>
