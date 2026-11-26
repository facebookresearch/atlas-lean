# Sharp blow-up threshold for degenerate two-species cross attraction

**System.** In $\mathbb{R}^d$, $d\ge3$, with $\alpha_1,\alpha_2\in(0,1]$, $p=\frac{2d}{d+2}$,

$$\partial_tu=\alpha_1\tfrac{d-2}{d}\|u\|_p^{\frac{4}{d+2}}\Delta\bigl(u^{p}\bigr)-\nabla\cdot(u\nabla v),\quad -\Delta v=w,$$

$$\partial_tw=\alpha_2\tfrac{d-2}{d}\|w\|_p^{\frac{4}{d+2}}\Delta\bigl(w^{p}\bigr)-\nabla\cdot(w\nabla z),\quad -\Delta z=u,$$

where $u$ (macrophages) follows the signal $v=K*w$ produced by $w$ (tumor cells) and vice versa, $K(x)=c_d|x|^{2-d}$ with $c_d$ the inverse surface area of $S^{d-1}$. Initial data are nonnegative, in $L^1((1+|x|^2)dx)\cap L^\infty$, with $\nabla u_0^{p},\nabla w_0^{p}\in L^2$. Masses are conserved and

$$E_\alpha[u,w]=\alpha_1\|u\|_p^2+\alpha_2\|w\|_p^2-c_d\iint\frac{u(x)w(y)}{|x-y|^{d-2}}\,dx\,dy$$

is a free energy.

**Theorem.** Let $C_{HLS}$ be the sharp Hardy–Littlewood–Sobolev constant for $\iint u(x)w(y)|x-y|^{2-d}\le C_{HLS}\|u\|_p\|w\|_p$.
1. For any mass, a free-energy solution exists locally; if it ceases to exist at $T_{\max}<\infty$ then $\|u\|_\infty+\|w\|_\infty\to\infty$.
2. If $\dfrac{2\sqrt{\alpha_1\alpha_2}}{c_d}\ge C_{HLS}$, there is a global free-energy solution.
3. If $\dfrac{2\sqrt{\alpha_1\alpha_2}}{c_d}<C_{HLS}$, there are initial data for which the free-energy solution blows up in finite time.

The threshold involves only the product $\alpha_1\alpha_2$ of the diffusion strengths, not the masses, because the nonlocal diffusion coefficients make the problem mass-invariant.

## Expansion

Writing $E_\alpha=(\sqrt{\alpha_1}\|u\|_p-\sqrt{\alpha_2}\|w\|_p)^2+\bigl(2\sqrt{\alpha_1\alpha_2}\|u\|_p\|w\|_p-c_dH[u,w]\bigr)$ shows that under the threshold condition both terms are nonnegative by the HLS inequality, so the dissipated energy bounds $\|u\|_p,\|w\|_p$, which rules out concentration and yields global existence. When the condition fails, choosing data close to HLS optimizers makes $E_\alpha$ negative, and the second moment $\int|x|^2(u+w)$ then decreases at a rate bounded by a negative multiple of the energy, forcing it to vanish in finite time, which is incompatible with global existence.

## Sources

- S. Ulusoy, "Sharp blow-up condition for a two-species cross attraction system in 3 or more dimensions", arXiv:2610.09078 (2026), Section 1 (system (1.1), data, free energy and threshold condition (1.12)), Theorem 1.1, Theorems 2.6–2.7 and Theorem 3.2, <https://doi.org/10.48550/arXiv.2610.09078>.
