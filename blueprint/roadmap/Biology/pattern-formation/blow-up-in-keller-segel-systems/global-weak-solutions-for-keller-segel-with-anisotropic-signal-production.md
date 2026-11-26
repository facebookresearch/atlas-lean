# Global weak solutions for Keller–Segel with anisotropic signal production

**Model.** In a smooth bounded domain $\Omega\subset\mathbb R^n$, $n\in\mathbb N$, with homogeneous Neumann conditions, consider
$$u_t=\nabla\cdot\bigl((u+1)^{m_1-1}\nabla u\bigr)-\nabla\cdot(u\nabla v),\qquad v_t=\nabla\cdot\bigl((v+1)^{m_2-1}\nabla v\bigr)+\nabla\cdot(u\nabla v)-v+u .$$
Here $u$ is a cell density and $v$ a signal; the term $\nabla\cdot(u\nabla v)$ in the signal equation models local anisotropy of the production (cells moving up the gradient carry signal with them). The case $m_1=m_2=1$ was treated by Tao and Winkler.

**Theorem.** Assume $u_0\in L^2(\Omega)$ and $v_0\in C^0(\overline\Omega)$ are nonnegative and
$$m_1>\frac n2,\qquad m_1\ge2,\qquad m_2\ge1 .$$
Then there is a global weak solution $(u,v)$, and a constant $C>0$ such that
$$\|u(\cdot,t)\|_{L^{m_1}(\Omega)}+\|v(\cdot,t)\|_{L^\infty(\Omega)}\le C\qquad\text{for a.e. } t>0 .$$

## Expansion

Adding the two equations cancels both cross terms: $(u+v)_t$ is a pure (nonlinear) diffusion plus $u-v$, which gives the $L^\infty$ bound on $v$ through a comparison argument and a maximum principle once $u$ is controlled. The porous-medium exponent $m_1>n/2$ makes the cell diffusion strong enough that an $L^{m_1}$ energy estimate for $u$ absorbs the chemotactic flux. The weak solution is obtained as a limit of classical solutions of an approximating system with a regularized cross term, which are global and bounded uniformly in the regularization.

## Sources

- Max Hegenbart, "Global existence of weak solutions in a Keller-Segel system with local anisotropy and nonlinear diffusion", arXiv:2610.11462 (2026), Theorem 1.1 and Sections 3–6, <https://doi.org/10.48550/arXiv.2610.11462>.
