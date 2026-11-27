# Boundary equilibria of sensitive–resistant Darwinian dynamics

**Model.** Sensitive cells $x_S$, resistant cells $x_R$ and the resistance strategy $u_R\ge 0$ of resistant cells (sensitive cells have $u_S=0$) evolve as

$$\dot x_S=x_S\Big[r_{\max}\Big(1-\tfrac{\alpha_{SS}x_S+\alpha_{SR}x_R}{K}\Big)-d-\tfrac mk\Big],\qquad \dot x_R=x_R\,G(v,u,x,m)\big|_{v=u_R},\qquad \dot u_R=\sigma\,\partial_vG(v,u,x,m)\big|_{v=u_R},$$

with fitness-generating function $G(v,u,x,m)=r_{\max}e^{-gv}\big(1-\tfrac{\alpha_{RS}x_S+\alpha_{RR}x_R}{K}\big)-d-\tfrac{m}{k+bv}$. Here $g>0$ is the cost of resistance, $b>0$ its benefit, $k\ge 1$ innate resistance, $m\ge 0$ the drug dose, $\sigma>0$ the evolutionary speed and $\alpha_{ij}>0$ competition coefficients. Write $c_S(m)=r_{\max}-d-m/k$, $c_R(u,m)=r_{\max}e^{-gu}-d-m/(k+bu)$, $c_{SS}=r_{\max}/K$, $c_{RR}(u)=r_{\max}e^{-gu}/K$ and $D=\alpha_{SS}\alpha_{RR}-\alpha_{SR}\alpha_{RS}$.

Let $u_R^*(m)$ be the singular resistance level of [Interior equilibrium of sensitive–resistant Darwinian dynamics](interior-equilibrium-of-sensitive-resistant-darwinian-dynamics.md) and $\kappa(u,m)=\alpha_{SS}c_R(u,m)/c_{RR}(u)-\alpha_{RS}c_S(m)/c_{SS}$ (so $x_R^*=\kappa(u_R^*,m)/D$).

**Theorem 2 (trivial equilibria).** A trivial equilibrium $(0,0,u_R^\diamond)$ has $u_R^\diamond$ solving $g\,r_{\max}e^{-gu}=bm/(k+bu)^2$, which has zero, one or two solutions. Its eigenvalues are $c_S(m)$, $c_R(u_R^\diamond,m)$ and $\sigma\frac{bm}{(k+bu_R^\diamond)^2}\big(g-\frac{2b}{k+bu_R^\diamond}\big)$; it is locally stable if $c_S(m)<0$, $c_R(u_R^\diamond,m)<0$ and $k+bu_R^\diamond<2b/g$.

**Theorem 3 (fully sensitive equilibria).** The equilibrium $(x_S^\dagger,0,u_R^\dagger)$ has $x_S^\dagger=\frac{K}{\alpha_{SS}}\big(1-\frac{d+m/k}{r_{\max}}\big)$ and $u_R^\dagger$ solving $g\,r_{\max}e^{-gu}(1-\alpha_{RS}x_S^\dagger/K)=bm/(k+bu)^2$; it exists only if $0<c_S(m)<r_{\max}\alpha_{SS}/\alpha_{RS}$. Its eigenvalues are $-c_S(m)$, $\frac{c_{RR}(u_R^\dagger)}{\alpha_{SS}}\kappa(u_R^\dagger,m)$ and $\sigma bm\,(g(k+bu_R^\dagger)-2b)/(k+bu_R^\dagger)^3$, so it is locally stable if $c_S(m)>0$, $\kappa(u_R^\dagger,m)<0$ and $k+bu_R^\dagger<2b/g$.

**Theorem 4 (fully resistant equilibrium).** At $(0,x_R^\ddagger,u_R^\ddagger)$ one has $u_R^\ddagger=u_R^*(m)$ and $x_R^\ddagger=\frac{K}{\alpha_{RR}}\big(1-\frac{e^{gu_R^*}}{r_{\max}}(d+\frac{m}{k+bu_R^*})\big)$, which requires $c_R(u_R^*,m)>0$. Its eigenvalues are $c_{SS}D\,x_S^*/\alpha_{RR}$, $-c_R(u_R^*,m)$ and a negative $\lambda_3$, so it is locally stable if $c_R(u_R^*,m)>0$ and $D\,x_S^*<0$, and unstable if $D\,x_S^*>0$, where $x_S^*$ is the (possibly negative) interior formula.

**Corollary (competition-ratio diagram).** When $c_S(m)>0$, set $\Gamma=e^{gu_R^*}c_R(u_R^*,m)/c_S(m)$. A stable fully resistant equilibrium requires $\alpha_{RR}/\alpha_{SR}<\Gamma$; at least one stable fully sensitive equilibrium exists when $\Gamma<\alpha_{RS}/\alpha_{SS}<r_{\max}/c_S(m)$ and none when $\alpha_{RS}/\alpha_{SS}>r_{\max}/c_S(m)$; and when $\alpha_{RR}/\alpha_{SR}>\Gamma$ and $\alpha_{RS}/\alpha_{SS}<\Gamma$ the stable state is the interior one.

## Depends on

- [Interior equilibrium of sensitive–resistant Darwinian dynamics](interior-equilibrium-of-sensitive-resistant-darwinian-dynamics.md)

## Expansion

On each face the Jacobian is block triangular, so the eigenvalues are the diagonal growth rates of the missing types plus the curvature $\sigma\partial_v^2G$ of the fitness landscape at the current strategy. With $x_S=0$, the conditions $G=0$ and $\partial_vG=0$ combine into $\Xi(u_R,m)=0$, so by Lemma 1 the fully resistant strategy coincides with the interior singular strategy and inherits $k+bu_R^*<2b/g$. The invasion eigenvalue of sensitive cells there is $c_S-c_{SS}\alpha_{SR}x_R^\ddagger$, which equals $c_{SS}Dx_S^*/\alpha_{RR}$ after substituting $x_R^\ddagger$. In the fully sensitive state the strategy equation need not coincide with $\Xi=0$ because $x_R=0$ removes the constraint $G=0$; the resistance level is set by the sensitive population's competitive pressure. The resulting picture in the plane of competition ratios $(\alpha_{RS}/\alpha_{SS},\alpha_{RR}/\alpha_{SR})$ separates interior, fully sensitive, fully resistant and bistable outcomes.

## Sources

- Satouri M, Rezaei J, Staňková K, "Stability of the Darwinian Dynamics: Effect of Intraspecific Competition and Human Intervention" (2025), Theorems 2, 3 and 4, equations (19)-(53) and Fig. 1, <https://doi.org/10.1007/s13235-025-00629-3>, PMCID PMC12460579.
