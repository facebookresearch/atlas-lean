# Local limit of nonlocal hapto- and chemotaxis systems

On a bounded smooth domain $\Omega\subset\mathbb R^n$, let $\mathcal R_r$ be either the [averaged-gradient operator](adhesion-velocity-as-averaged-gradient.md) $\mathcal T_r$ or its sphere-average analogue $\mathcal S_r$ for the nonlocal chemotactic gradient, and consider for $r\in(0,r_0]$

$$\partial_tc_r=\nabla\cdot\Big(D_c(c_r,v_r)\nabla c_r-c_r\chi(c_r,v_r)\,\mathcal R_r\big(\nabla g(c_r,v_r)\big)\Big)+f_c(c_r,v_r),\qquad \partial_tv_r=D_v\Delta v_r+f_v(c_r,v_r),$$

with no-flux boundary conditions, $D_v\ge0$, and nonnegative initial data $c_0\in L^2(\Omega)$, $v_0\in H^1(\Omega)$. The local system is the case $\mathcal R_0=\mathrm{id}$:

$$\partial_tc=\nabla\cdot\big(D_c\nabla c-c\chi\nabla g(c,v)\big)+f_c,\qquad \partial_tv=D_v\Delta v+f_v,$$

that is, a haptotaxis ($D_v=0$) or chemotaxis ($D_v>0$) system with effective diffusion $D_c-c\chi\partial_cg$ and sensitivity $\chi\partial_vg$. Assume bounded continuous $D_c,\chi$, continuously differentiable $g,f_c,f_v$ satisfying the paper's growth and positivity bounds, either Lipschitz or dissipative $f_c$, and a smallness condition on the operator norms of $\mathcal R_r$ relative to $\chi$ and $\nabla g$. Then there exist a sequence $r_m\to0$, global nonnegative weak–strong solutions $(c_{r_m},v_{r_m})$ of the nonlocal systems and a weak–strong solution $(c,v)$ of the local system with

$$c_{r_m}\to c,\qquad v_{r_m}\to v\qquad\text{in }L^2\big(0,T;L^2(\Omega)\big)\ \text{for every }T>0.$$

## Depends on

- [Adhesion velocity as an averaged gradient](adhesion-velocity-as-averaged-gradient.md)
- [Keller–Segel flux](../turing-instability-with-cross-diffusion/keller-segel-flux.md)

## Expansion

Global existence for each $r$ is proved by a fixed point on a frozen linear problem with a monotone operator, followed by a priori bounds; the smallness condition keeps the nonlocal drift from overwhelming diffusion. The bounds on $c_r$ in $L^2(0,T;H^1)$ and on $v_r$ in $C([0,T];H^1)$ are uniform in $r$, so compactness arguments give strongly convergent subsequences. Strong $L^p$ convergence of $\mathcal R_r$ to the identity, self-adjointness and compensated compactness then pass to the limit in the nonlocal flux. Using $\mathcal T_r(\nabla\cdot)$ rather than $\mathcal A_r$ avoids spurious boundary-layer concentration.

## Sources

- M. Eckardt, K. J. Painter, C. Surulescu, A. Zhigun, "Nonlocal and local models for taxis in cell migration: a rigorous limit procedure", J. Math. Biol. 81 (2020), Section 5, Assumptions 5.1–5.4, Definition 5.6, Theorems 5.8, 5.10 and 5.13, <https://doi.org/10.1007/s00285-020-01536-4>, PMCID PMC7716906.
