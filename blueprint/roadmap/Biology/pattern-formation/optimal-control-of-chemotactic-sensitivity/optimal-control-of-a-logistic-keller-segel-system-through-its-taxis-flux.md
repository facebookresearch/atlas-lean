# Optimal control of a logistic Keller–Segel system through its taxis flux

**State system.** On a bounded $C^2$ domain $\Omega\subset\mathbb{R}^2$, $\Omega_T=\Omega\times(0,T)$, with Neumann conditions,
$$\partial_tu-D_u\Delta u+\nabla\cdot(f\,u\nabla v)=ru-\mu u^2,\qquad \partial_tv-D_v\Delta v+\alpha v=\beta u,$$
where $u$ is the cell density, $v$ the chemoattractant, and the control $f(x,t)$ is the chemotactic sensitivity, taken in the admissible set $\mathcal{F}=\{f\in L^4(\Omega_T):\xi_1\le f\le\xi_2\text{ a.e.}\}$ for given bounds $\xi_1\le\xi_2$ in $L^\infty$.

**Cost.**
$$J(u,v,f)=\gamma_u\int_0^T\|u-u_d\|_{L^2}^2dt+\gamma_{\mathrm{taxis}}\int_0^T\|f\,u\nabla v\|_{L^2}^2dt+\gamma_f\int_0^T\|f\|_{L^4}^4dt+\gamma_T\|u(T)-u_T\|_{L^2}^2,$$
combining tracking of a target density $u_d$, penalization of the taxis flux, control cost and a terminal target $u_T$.

**Theorems.**
1. *(Well-posedness.)* For $u_0\in L^4(\Omega)$, $v_0\in W^{3/2,4}_{\mathbf n}(\Omega)$, $u_0,v_0\ge0$, and $f\in\mathcal{F}$, the state system has a unique weak solution with
$u\in L^\infty(0,T;L^4)\cap L^2(0,T;H^1)$, $\partial_tu\in L^2(0,T;(H^1)')$, $v\in C([0,T];W^{3/2,4}_{\mathbf n})\cap L^4(0,T;W^{2,4})$, $\partial_tv\in L^4(\Omega_T)$, bounded by a constant depending on the data and the bounds of $\mathcal{F}$.
2. *(Existence of optimal controls.)* The problem $\min J$ over admissible triples has at least one solution.
3. *(First-order conditions.)* At a local optimum $(\tilde u,\tilde v,\tilde f)$ there is a Lagrange multiplier $(\lambda,\eta)\in L^2(0,T;H^1)\times L^{4/3}(\Omega_T)$ solving the backward adjoint system
$$-\partial_t\lambda-D_u\Delta\lambda-\tilde f\nabla\tilde v\cdot\nabla\lambda-r\lambda+2\mu\tilde u\lambda-\beta\eta=2\gamma_u(\tilde u-u_d)+2\gamma_{\mathrm{taxis}}|\tilde f|^2\tilde u|\nabla\tilde v|^2,$$
$$-\partial_t\eta-D_v\Delta\eta+\alpha\eta+\nabla\cdot(\tilde f\tilde u\nabla\lambda)=-2\gamma_{\mathrm{taxis}}\nabla\cdot(|\tilde f|^2|\tilde u|^2\nabla\tilde v),$$
with Neumann and terminal conditions, together with a variational inequality characterizing $\tilde f$ over the critical cone of $\mathcal{F}$.

## Expansion

Well-posedness is obtained by regularizing the problem with a parameter $\varepsilon$, solving it by Schauder's fixed-point theorem, deriving $\varepsilon$-independent positivity and a priori bounds (using maximal $L^p$–$L^q$ regularity of the Neumann heat equation for $v$ and the logistic damping $-\mu u^2$ for $u$), passing to the limit and proving uniqueness by an energy estimate. Existence of an optimum follows from the direct method: the quartic control cost gives weak compactness in $L^4$, and the state bounds give strong convergence of the nonlinear taxis term. The optimality system comes from a Lagrange multiplier theorem at a regular point of the constraint map, after showing differentiability of the control-to-state map.

## Sources

- Y. Simpore, M. Warma, L. P. Yapu, "Optimal control via chemotactic sensitivity of a logistic Keller-Segel model", arXiv:2609.18030 (2026), Section 1 (state system, admissible set, cost and control problem), Theorems 1.2 and 1.3, Theorem 2.2, Theorem 5.2, Corollary 5.3 and Proposition 5.4, <https://doi.org/10.48550/arXiv.2609.18030>.
