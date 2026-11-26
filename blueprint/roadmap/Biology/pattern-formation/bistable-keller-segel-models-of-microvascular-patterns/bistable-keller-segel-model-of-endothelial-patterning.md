# Bistable Keller-Segel model of endothelial patterning

**Model.** On a bounded domain $\Omega\subset\mathbb R^n$ ($n=2,3$) with Neumann boundary conditions, endothelial cell density $u$ and a chemoattractant (signalling substrate) $v$ satisfy

$$u_t=f(u)-b\,\nabla\!\cdot(u\nabla v)+d_u\Delta u,\qquad v_t=cu-ev+d_v\Delta v,\qquad f(u)=au(1-u)(u-\gamma),$$

with $0<\gamma<1$. The bistable kinetics make $0$ and $1$ stable and $\gamma$ a threshold, so the dish separates into cell-covered ($u\approx1$) and empty ($u\approx0$) regions, while chemotaxis of strength $b$ aggregates cells into vessel-like patterns.

**Kinetics.** The ODE $u'=f(u)$, $v'=cu-ev$ has equilibria $(0,0)$, $(\gamma,\frac ce\gamma)$ and $(1,\frac ce)$; the outer two are stable nodes, and $u=\gamma$ separates their basins ($u_0<\gamma\Rightarrow u\to0$, $u_0>\gamma\Rightarrow u\to1$). Smooth non-negative initial data give non-negative solutions. Spatial means obey $\bar u_t=\int_\Omega f(u)$ and $\bar v_t=c\bar u-e\bar v$, so stationary patterns must satisfy $\int_\Omega f(u)=0$ and $\bar v=\frac ce\bar u$.

**Theorem (stability of homogeneous states).** The empty state $(0,0)$ is exponentially stable: solutions of the linearization satisfy $\|(u,v)(t)\|_{L^2}\le e^{-\mu t}\|(u,v)(0)\|_{L^2}$, and there are $\eta,\mu>0$ such that $\|U(0)\|_{H^2}<\eta$ implies $\|U(t)\|_{H^2}\le e^{-\mu t}\|U(0)\|_{H^2}$ for the nonlinear system. The fully covered state $(1,\frac ce)$ is exponentially stable, linearly and nonlinearly in $H^2$, provided that, for every Neumann eigenvalue $\lambda_k$ of $-\Delta$,

$$d_ud_v\lambda_k^2+\big(d_ue+(1-\gamma)d_v-bc\big)\lambda_k+(1-\gamma)e>0,$$

with the reaction scaled as in the source. Strong chemotaxis $bc$ violates this condition and destabilizes the covered state, which is the mechanism of pattern formation.

**Theorem (two-compartment analog).** In the coupled ODE model with cells moving between two compartments by discrete diffusion and discrete chemotactic flux,

$$u_1'=f(u_1)-bu_1(v_2-v_1)+d_u(u_2-u_1),\qquad v_1'=cu_1-ev_1+d_v(v_2-v_1),$$

and symmetrically for $(u_2,v_2)$, the positive cone is invariant and the system is dissipative. Equilibria satisfy $u_2=\phi(u_1)$, $u_1=\phi(u_2)$ with $\phi(u)=u+f(u)/\big(\frac{bc}{e+2d_v}u-d_u\big)$. Under explicit non-degeneracy conditions, the symmetric equilibrium undergoes a non-degenerate **symmetry-breaking pitchfork bifurcation** at a critical chemotactic strength $b_*$, and the asymmetric equilibria undergo a non-degenerate saddle-node bifurcation, so four stable equilibria can coexist: empty, full, and two mirror-image segregated states.

## Depends on

- [Turing patterns and diffusion-driven instability](../turing-patterns-and-diffusion-driven-instability/README.md)

## Expansion

Linearizing at a homogeneous state and expanding in Neumann eigenfunctions gives, for each mode $k$, a $2\times2$ matrix whose determinant is the quadratic above; positivity for all $k$ (with negative trace) means every mode decays, and the chemotactic term $-bc\lambda_k$ is the only destabilizing contribution, so pattern onset is a chemotaxis-driven instability analogous to a Turing instability. Nonlinear stability in $H^2$ follows from the spectral gap together with Sobolev embeddings controlling the quadratic chemotactic term. In the two-compartment model, the exchange symmetry $(u_1,v_1)\leftrightarrow(u_2,v_2)$ forces the pitchfork, and the normal-form coefficients are computed explicitly. Simulations reproduce three temporal phases of microvascular network formation, and a data-driven chemoattractant equation reproduces the observed timing.

## Sources

- B. Ambrosio, A. Garroudji, S. Fitzsimons, H. Zaag, "On a Keller-Segel type equation to model brain microvascular endothelial cells growth's patterns", arXiv:2604.25180 (2026), Section 2 (modified Keller-Segel model, Propositions 1-2, 4-5, Theorem 6) and Section 6 (Propositions 7-8, Theorems 9-10), <https://doi.org/10.48550/arXiv.2604.25180>.
