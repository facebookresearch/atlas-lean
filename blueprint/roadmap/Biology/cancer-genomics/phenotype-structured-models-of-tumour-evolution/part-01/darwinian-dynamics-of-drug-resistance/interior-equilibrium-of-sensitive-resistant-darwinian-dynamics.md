# Interior equilibrium of sensitive–resistant Darwinian dynamics

**Model.** Sensitive cells $x_S$, resistant cells $x_R$ and the resistance strategy $u_R\ge 0$ of resistant cells (sensitive cells have $u_S=0$) evolve as

$$\dot x_S=x_S\Big[r_{\max}\Big(1-\tfrac{\alpha_{SS}x_S+\alpha_{SR}x_R}{K}\Big)-d-\tfrac mk\Big],\qquad \dot x_R=x_R\,G(v,u,x,m)\big|_{v=u_R},\qquad \dot u_R=\sigma\,\partial_vG(v,u,x,m)\big|_{v=u_R},$$

with fitness-generating function $G(v,u,x,m)=r_{\max}e^{-gv}\big(1-\tfrac{\alpha_{RS}x_S+\alpha_{RR}x_R}{K}\big)-d-\tfrac{m}{k+bv}$. Here $g>0$ is the cost of resistance, $b>0$ its benefit, $k\ge 1$ innate resistance, $m\ge 0$ the drug dose, $\sigma>0$ the evolutionary speed and $\alpha_{ij}>0$ competition coefficients. Write $c_S(m)=r_{\max}-d-m/k$, $c_R(u,m)=r_{\max}e^{-gu}-d-m/(k+bu)$, $c_{SS}=r_{\max}/K$, $c_{RR}(u)=r_{\max}e^{-gu}/K$ and $D=\alpha_{SS}\alpha_{RR}-\alpha_{SR}\alpha_{RS}$.

**Singular resistance level.** At any equilibrium with $x_R>0$ (so $G=0$) the condition $\partial_vG=0$ reduces to $\Xi(u_R,m)=0$, where

$$\Xi(u,m)=-gd-\frac{gm}{k+bu}+\frac{bm}{(k+bu)^2},\qquad u_R^*(m)=-\frac kb+\frac{-mg+\sqrt{m^2g^2+4mgdb}}{2bdg}.$$

**Lemma 1.** $\Xi(u,m)(k+bu)^2=-gb\,(u-u_R^*)\big(d(2k+bu+bu_R^*)+m\big)$, so $\Xi>0$ for $u<u_R^*$ and $\Xi<0$ for $u>u_R^*$; $u_R^*>0$ iff $k^2dg+kmg<mb$.

**Interior equilibrium.** An interior equilibrium $(x_S^*,x_R^*,u_R^*)$ has

$$x_R^*=\frac{\alpha_{SS}c_R(u_R^*,m)/c_{RR}(u_R^*)-\alpha_{RS}c_S(m)/c_{SS}}{D},\qquad x_S^*=\frac{\alpha_{RR}c_S(m)/c_{SS}-\alpha_{SR}c_R(u_R^*,m)/c_{RR}(u_R^*)}{D},$$

and exists only if $c_S(m)>0$, whatever the sign of $D$ (and $D\neq 0$).

**Theorem 1.** If the interior equilibrium exists and $D>0$, it is locally asymptotically stable. Its Jacobian eigenvalues are

$$\lambda_{1,2}=\tfrac12\Big(-\big(c_{RR}\alpha_{RR}x_R^*+c_{SS}\alpha_{SS}x_S^*\big)\pm\sqrt{\big(c_{RR}\alpha_{RR}x_R^*+c_{SS}\alpha_{SS}x_S^*\big)^2-4c_{SS}c_{RR}x_S^*x_R^*D}\Big),\qquad \lambda_3=\frac{\sigma bm\,\big(g(k+bu_R^*)-2b\big)}{(k+bu_R^*)^3},$$

and $\lambda_3<0$ always, because $k+bu_R^*<2b/g$. If $D<0$ the equilibrium is a saddle.

## Expansion

Because $\partial_vG=0$ at an equilibrium, the $u_R$-column of the Jacobian has a single nonzero entry $\sigma\partial^2_vG$, so the spectrum splits into the $2\times 2$ Lotka–Volterra block and $\lambda_3$. The block has negative trace and determinant $c_{SS}c_{RR}x_S^*x_R^*D$, giving the dichotomy in $D$. Using $G=0$ to eliminate $e^{-gu}$ from $\partial_v^2G$ gives the closed form of $\lambda_3$; with $y=k+bu_R^*$ solving $gdy^2+gmy-bm=0$, one checks $2b/g-y=\big(4bd+gm-\sqrt{g^2m^2+4gbdm}\big)/(2dg)>0$ since $(4bd+gm)^2>g^2m^2+4gbdm$. The existence argument shows that $c_S(m)\le 0$ would force both competition ratios to contradict the sign of $D$. Biologically, the singular strategy depends only on cost, benefit, death rate and dose, not on competition, and the interior (coexistence) state is stable exactly when intraspecific competition dominates interspecific competition.

## Sources

- Satouri M, Rezaei J, Staňková K, "Stability of the Darwinian Dynamics: Effect of Intraspecific Competition and Human Intervention" (2025), system (4)-(6), equations (8)-(18), Lemma 1 and Theorem 1, <https://doi.org/10.1007/s13235-025-00629-3>, PMCID PMC12460579.
