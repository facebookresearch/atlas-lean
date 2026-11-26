# Global boundedness and blow-up time bound for a fish–mussel chemotaxis system

**Model.** In a smooth bounded domain $\Omega\subset\mathbb R^n$ with homogeneous Neumann boundary conditions, let $u$ be the nutrient concentration, $v$ the fish density and $w$ the mussel density, with $\tau\in\{0,1\}$:
$$\tau u_t=\Delta u-u(\alpha+\beta v+\gamma w)+f(x,t),$$
$$v_t=\Delta v-\chi\nabla\cdot(v\nabla u)+\sigma_1v(1-v+u)-\delta_1v,$$
$$\tau w_t=\Delta w+\sigma_2uw-\delta_2w.$$
Fish move up nutrient gradients (taxis coefficient $\chi>0$), nutrients are lost at rate $\alpha$ and consumed by fish and mussels, and the external nutrient input satisfies $f\in W^{1,\infty}$, $0\le f\le M$, $|\nabla f|\le M$. Initial data are nonnegative with $v_0$ continuous and $\tau u_0,\tau w_0\in W^{1,q}$, $q>n$.

**Theorem (global boundedness).** Let $n\ge3$ and all parameters be positive. If
$$\max\Big\{\tau\|u_0\|_{L^\infty},\ \frac{M}{\alpha}\Big\}<\min\Big\{\frac{\pi}{\chi}\sqrt{\frac2n},\ \frac{\delta_2}{\sigma_2}\Big\},$$
then there is a unique global classical solution with $\|u(t)\|_{W^{1,q}}+\|v(t)\|_{L^\infty}+\|w(t)\|_{W^{1,q}}\le C$ for all $t>0$.

**Theorem (lower bound on blow-up time).** Let $\Omega\subset\mathbb R^3$ be convex. If a solution blows up at $T_{\max}<\infty$ in the sense $\limsup_{t\to T_{\max}}\|v(t)\|_{L^\infty}=\infty$, then with
$$\Psi_\tau(t)=\tau\int_\Omega|\nabla u|^4+\int_\Omega v^2+\tau\int_\Omega|\nabla w|^2$$
there are computable constants with
$$T_{\max}\ge\int_{\Psi_\tau(0)}^{\infty}\frac{d\Psi}{\mathcal A_\tau\Psi^3+\mathcal B_\tau\Psi^{3/2}+\mathcal C_\tau\Psi^{\tau}+\tau\mathcal D_\tau}\ \ge\ \frac{1}{2\mathcal E_\tau\Psi_\tau(0)^2}.$$

## Expansion

The comparison principle gives $u\le\max\{\tau\|u_0\|_\infty,M/\alpha\}$, which keeps the nutrient (the chemoattractant) uniformly small. Smallness below $\delta_2/\sigma_2$ makes the mussel growth rate $\sigma_2u-\delta_2$ negative, so $w$ stays bounded; smallness below $\frac{\pi}{\chi}\sqrt{2/n}$ is the threshold under which the weighted functional $\int v^p\varphi(u)$ with a trigonometric weight $\varphi$ decays, which is the standard route to boundedness in chemotaxis–consumption systems. $L^p$ bounds on $v$ for large $p$ then give $L^\infty$ bounds by semigroup estimates. For the blow-up time, differentiating $\Psi_\tau$ and using Sobolev and Gagliardo–Nirenberg inequalities on a convex domain (where boundary terms from $\partial_\nu|\nabla u|^2\le0$ have a sign) yields $\Psi'\le\mathcal A\Psi^3+\mathcal B\Psi^{3/2}+\dots$, and integrating this differential inequality gives the lower bound on $T_{\max}$.

## Sources

- Gnanasekaran Shanmugasundaram, Jitraj Saha, "Global existence, blow-up behavior and numerical simulations for a class of chemotaxis-driven fish-mussel systems", arXiv:2606.18695 (2026), Theorems 1.1 and 1.2, <https://doi.org/10.48550/arXiv.2606.18695>.
