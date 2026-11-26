# Travelling waves of a two-population free-boundary cell-mechanics model

**Model.** In one space dimension, cells of population $A$ (proliferating, occupying $(s_0,s_1(t))$) and population $B$ (non-proliferating, occupying $(s_1(t),s_2(t))$) interact through nearest-neighbour forces $F_A,F_B$ of the inter-cell distance and move with drag coefficients $\eta_A,\eta_B$. The continuum limit of the individual-based model gives, for the cell densities $\rho_A,\rho_B$,

$$
\partial_t\rho_A=\partial_x\big(D_A(\rho_A)\partial_x\rho_A\big)+G(\rho_A)\rho_A\ \ \text{in }(s_0,s_1(t)),\qquad \partial_t\rho_B=\partial_x\big(D_B(\rho_B)\partial_x\rho_B\big)\ \ \text{in }(s_1(t),s_2(t)),
$$

with nonlinear diffusivities

$$
D_l(\rho)=-\frac{F_l'(1/\rho)}{\eta_l\,\rho^2},\qquad l=A,B,
$$

a density-dependent growth rate $G$, the transmission conditions $\frac1{\eta_A}F_A(1/\rho_A)=\frac1{\eta_B}F_B(1/\rho_B)$ (force balance) and continuity of flux at the interface $s_1$, a no-flux condition at $s_0$, and kinematic laws for the free boundaries, e.g. $\dot s_2=\frac{2}{\eta_B}F_B(1/\rho_B)$ at $x=s_2(t)$. The forces are repulsive above an equilibrium density $\rho_l^{\rm eq}$, so $D_l>0$ there.

**Theorem (existence).** Under regularity and sign assumptions on $F_l$, $D_l\ge d_l>0$ above $\rho_l^{\rm eq}$, $G\in C^3$ satisfying the source's sign conditions, and compatible initial data with $\rho_l^0\ge\rho_l^{\rm eq}$, the free-boundary problem has a solution with $s_1,s_2\in W^{1,3}(0,T)$, $\rho_l\in H^1(0,T;L^2)\cap L^2(0,T;H^2)$ on the moving domains, and $\rho_l\ge\rho_l^{\rm eq}$.

**Theorem (travelling waves).** For every mass $M>0$ of population $B$ there are a speed $c>0$ and a width $\ell>0$ and a travelling-wave solution in $z=x-ct$ with $\rho_A(z)\to\rho^{\rm M}$ as $z\to-\infty$ (the homeostatic density where $G$ vanishes) and $\int_0^\ell\rho_B=M$, such that $\rho_A$ is decreasing on $(-\infty,0)$ with $\rho_A^{\rm eq}<\rho_A(0)<\rho_A(z)<\rho^{\rm M}$, and $\rho_B$ is decreasing on $(0,\ell)$ with $\rho_B^{\rm eq}<\rho_B(\ell)<\rho_B(z)<\rho_B(0)$. If $F_A=F_B$, the density jump at the interface satisfies

$$
\operatorname{sgn}\big(\rho_A(0)-\rho_B(0)\big)=\operatorname{sgn}(\eta_A-\eta_B).
$$

## Expansion

Labelling cells by a continuous index and passing to the limit of small cell spacing turns Newton's law with overdamped drag into a nonlinear diffusion for the inverse spacing (the density), with diffusivity given by the stiffness of the force law; the population boundaries become free boundaries moving with the cells at the edge. The proliferating population pushes the passive one, so the whole tissue invades with speed set by the proliferation flux. At the interface force balance equates $F_A/\eta_A$ and $F_B/\eta_B$; with identical force laws the more strongly anchored (higher-drag) population is compressed more, which gives the jump condition. Simulations of the individual-based model agree with the free-boundary solutions, justifying the continuum description.

## Sources

- Tommaso Lorenzi, Philip J. Murray, Mariya Ptashnyk, "From individual-based mechanical models of multicellular systems to free-boundary problems", arXiv:1903.06590: Section 2 (individual-based model and derivation of the free-boundary problem), Section 3: Assumption 3.1, Definition 3.2, Theorem 3.3 (existence); Section 4: Theorem 4.1 (travelling waves). <https://doi.org/10.48550/arXiv.1903.06590>
