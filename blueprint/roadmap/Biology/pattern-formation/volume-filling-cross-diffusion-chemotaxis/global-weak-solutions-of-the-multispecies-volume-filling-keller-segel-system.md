# Global weak solutions of the multispecies volume-filling Keller–Segel system

Multiphase models of vascular network formation track the volume fractions $u_0,\dots,u_n$ of cell phases (with $u_0$ typically water) and signal concentrations $c_1,\dots,c_g$ on a bounded domain $\Omega\subset\mathbb R^d$:

$$\partial_tu_i=\nabla\cdot\Big(J_i-u_i\sum_{k=0}^nJ_k\Big),\quad J_i=\alpha_iu_i^{m_i-1}\nabla u_i+u_i\sum_{k=1}^g\chi_{ik}\nabla c_k,\qquad \partial_tc_j=D_j\Delta c_j-\lambda_jc_j+\sum_{k=0}^nb_{jk}u_k,$$

with no-flux boundary conditions and the saturation (volume-filling) constraint $\sum_{i=0}^nu_i=1$. Here $m_i\ge1$, $\alpha_0\ge0$, $\alpha_i>0$ ($i\ge1$), $D_j,\lambda_j>0$, $b_{jk}\ge0$, and $\chi_{ik}\in\mathbb R$ ($\chi_{ik}<0$ attraction, $\chi_{ik}>0$ repulsion). Data: $u^0(x)\in\overline{\mathcal D}$, $\mathcal D=\{u\in(0,1)^n:\sum_{i\ge1}u_i<1\}$, and $c^0\in H^1$ with $0\le c^0\le1$.

**Theorem.** For every $T>0$ and integer $\kappa>d/2$ there is a weak solution with $u_0=1-\sum_{i\ge1}u_i$, $u(x,t)\in\overline{\mathcal D}$, $c\ge0$, $u_i\in L^\infty$, $\alpha_iu_i^{m_i/2},c_j\in L^2(0,T;H^1)$ and $\partial_tu_i,\partial_tc_j\in L^2(0,T;(H^\kappa)')$. If $1\le m_i\le2$, weak solutions satisfying the entropy inequality coincide with any strictly positive strong solution with $\nabla\log\widehat u_i\in L^\infty$ and the same data (weak–strong uniqueness).

## Expansion

The system has an entropy

$$\bar h=\sum_{i=0}^nu_i(\log u_i-1)-\sum_{i,j}\frac{\chi_{ij}}{D_j}u_ic_j+\frac K2\sum_jc_j^2,$$

convex for large $K$. Because of the constraint, $\bar h''\bar A$ is only positive semidefinite in the full variables. Eliminating $u_0=1-\sum_{i\ge1}u_i$ removes the rank deficiency, and for large $K$ the entropy production dominates $\sum_i\frac{\alpha_i}{2}|\nabla u_i^{m_i/2}|^2+\sum_j|\nabla c_j|^2$. Volume filling keeps $u_i$ bounded, so the reaction terms are harmless, and an extension of the boundedness-by-entropy method (entropy variables, regularization, fixed point, Aubin–Lions compactness) works despite only partial volume filling and unbounded $c$. Weak–strong uniqueness uses the relative entropy and needs $m_i\le2$ so that the mixed term $u_i^2|\cdot|^2$ is absorbed by the degenerate production $u_i^{m_i}|\cdot|^2$.

## Sources

- N. Geltner, A. Jüngel, M. Zhang, *Analysis of a multispecies cross-diffusion Keller-Segel system with volume filling* (2026), Theorem 1 (existence) and Theorem 2 (weak–strong uniqueness); entropy structure in Section 2 and formal multiphase derivation in Appendix A. <https://doi.org/10.48550/arXiv.2607.12897>
