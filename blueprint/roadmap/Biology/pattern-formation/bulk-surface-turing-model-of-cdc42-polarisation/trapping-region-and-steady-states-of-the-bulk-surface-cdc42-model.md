# Trapping region and steady states of the bulk-surface Cdc42 model

**Setting.** Consider the reduced surface system $\partial_\tau u=\Delta_\Gamma u+\gamma f(u,v)$, $\partial_\tau v=d\Delta_\Gamma v+\gamma(-f(u,v)+q(u,v,V[u+v]))$ on the unit sphere $\Gamma$, with $f(u,v)=c_2v-u+u^2v$ and all rate parameters nonnegative. Spatial averaging replaces $V$ by $\bar V=V_0-a(\bar u+\bar v)$, where $a=|\Gamma|/|\Omega|=3$, and gives the homogeneous system

$$\frac{d\bar u}{d\tau}=\gamma f(\bar u,\bar v),\qquad \frac{d\bar v}{d\tau}=\gamma\bigl(-f(\bar u,\bar v)+q_0(\bar u,\bar v)\bigr),$$

$$q_0(\bar u,\bar v)=c_1a\,(c_{\max}-(\bar u+\bar v))\,(m-(\bar u+\bar v))-c_{-1}\bar v,\qquad m=V_0/a .$$

The source's Eq. (8) prints $d\bar v/d\tau=\gamma\bigl(f(\bar u,\bar v)-q_0(\bar u,\bar v)\bigr)$; the page writes $\gamma(-f+q_0)$ because that is the spatial average of the $v$-equation of the source's reduced model (6), $\partial_\tau v=d\Delta_\Gamma v+\gamma(-f+q)$, displayed above (the Laplacian averages to zero on the closed surface $\Gamma$).

The physically admissible states form

$$\mathcal A=\{(u,v)\ge(0,0):\ u+v\le\min(c_{\max},m)\}.$$

**Theorem.**

1. *(Well-posedness.)* For initial data with values in $\mathcal A$ and $\nabla_\Gamma u_0,\nabla_\Gamma v_0\in L^2(\Gamma)$, the reduced system has a unique global-in-time solution. The same holds on any open, bounded, regular domain in $\mathbb R^n$ with zero-flux boundary conditions.
2. *(Trapping region.)* $\mathcal A$ is positively invariant for the homogeneous system. This is not claimed for the full PDE.
3. *(Steady states.)* The homogeneous system has $0$, $2$, $4$ or $6$ positive steady states, and nonnegative parameters guarantee at least one steady state in $\mathcal A$. A steady state $(u^*,v^*)\in\mathcal A$ that admits diffusion-driven instability satisfies the necessary condition

$$\sqrt{c_2}<\min(c_{\max},m),\qquad u^*\in\bigl(\sqrt{c_2},\ \min(c_{\max},m)\bigr).$$

**Classic and non-classic instability.** Classic diffusion-driven instability turns a stable node of the homogeneous system into an unstable node once diffusion is added. In the non-classic case the stable node becomes a saddle, which can occur even for equal membrane diffusivities ($d=1$), where classic Turing patterns are impossible. Numerical maps of the $(c_{-1},c_2)$ and $(c_1,c_2)$ planes suggest that the non-classic region is the limit $d\to1$ of the classic one.

## Depends on

- [Bulk-surface activator–inhibitor model of Cdc42 polarisation](bulk-surface-activator-inhibitor-model-of-cdc42-polarisation.md)
- [Diffusion-driven instability (Turing 1952)](../turing-patterns-and-diffusion-driven-instability/turing-instability.md)

## Expansion

The two bounds in $\mathcal A$ encode that the cytosolic pool $\bar V$ and the remaining membrane capacity $c_{\max}-(\bar u+\bar v)$ are nonnegative. Invariance means trajectories of the homogeneous system cannot leave $\mathcal A$ through its boundary. At a steady state, $f(u^*,v^*)=0$ gives $v^*=u^*/(c_2+u^{*2})$, and substituting this into $q_0=0$ leaves a single polynomial equation in $u^*$. Then $f_u=-1+2u^*v^*=(u^{*2}-c_2)/(c_2+u^{*2})$ and $f_v=c_2+u^{*2}>0$, while diffusion-driven instability needs the activator to be self-enhancing, $f_u>0$, that is $u^*>\sqrt{c_2}$. So the necessary condition bounds a pattern-forming steady state below by $\sqrt{c_2}$, and above by the membrane capacity and the cytosolic supply. Simulations show that the number of poles grows with $\gamma$, and that pole size shrinks while peak active Cdc42 grows as $d$ increases. The proofs of items 1–3 are in the paper's Supplementary Text 1.3–1.6.

## Sources

- J. Borgqvist, A. Malik, C. Lundholm, A. Logg, P. Gerlee, M. Cvijovic, "Cell polarisation in a bulk-surface model can be driven by both classic and non-classic Turing instability", *npj Systems Biology and Applications* 7:13 (2021), Results, Eqs. (8)–(10), Theorems 1–3, Corollary 1, Fig. 2, <https://doi.org/10.1038/s41540-021-00173-x>, PMCID PMC7910310.
