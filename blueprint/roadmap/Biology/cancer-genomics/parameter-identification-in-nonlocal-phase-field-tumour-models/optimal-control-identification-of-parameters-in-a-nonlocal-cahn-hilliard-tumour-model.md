# Optimal-control identification of parameters in a nonlocal Cahn–Hilliard tumour model

On a bounded domain $\Omega\subset\mathbb R^d$ ($d=2,3$) and time interval $(0,T)$, let $\varphi$ be the tumour phase field ($\varphi=1$ tumour, $\varphi=-1$ healthy tissue), $\mu$ its chemical potential and $\sigma$ the nutrient concentration, governed by the nonlocal system

$$ \partial_t(\varepsilon\mu+\varphi)-\Delta\mu=(P\sigma-A)f(\varphi),\qquad \mu=\tau\partial_t\varphi+a\varphi-J*\varphi+F'(\varphi)-\chi\sigma,\qquad \partial_t\sigma-\Delta\sigma+B(\sigma-\sigma_S)+C\sigma f(\varphi)=-\eta\Delta\varphi, $$

with homogeneous Neumann conditions and initial data. Here $J$ is an even interaction kernel with $a=J*1$, $F$ a double-well potential (logarithmic or super-quadratic polynomial, on $(-\ell,\ell)$) with $a_*+F''\ge C_0>0$, $f\ge0$ bounded and Lipschitz (later $f\in C^2_b$), $P$ the proliferation rate, $A$ apoptosis, $B,\sigma_S$ nutrient supply, $C$ consumption, $\chi$ chemotaxis and $\eta$ active transport; $\varepsilon\in(0,\varepsilon_0)$ and $\tau\in(0,1)$ are parabolic and viscous regularizations. The unknown parameters $(P,\chi,\eta,C)$ range over the box $\mathcal U_{ad}=[0,P_{\max}]\times[0,\chi_{\max}]\times[0,\eta_{\max}]\times[0,C_{\max}]$ and are fitted by minimizing the tracking functional

$$ \mathcal J=\frac{\beta_\Omega}2\|\varphi(T)-\varphi_\Omega\|_{L^2(\Omega)}^2+\frac{\beta_Q}2\|\varphi-\varphi_Q\|_{L^2(Q)}^2+\frac{\alpha_P}2|P-P_*|^2+\frac{\alpha_\chi}2|\chi-\chi_*|^2+\frac{\alpha_\eta}2|\eta-\eta_*|^2+\frac{\alpha_C}2|C-C_*|^2 $$

with targets $\varphi_\Omega\in L^2(\Omega)$, $\varphi_Q\in L^2(Q)$, nonnegative weights not all zero and prior values $P_*,\chi_*,\eta_*,C_*\ge0$.

**Theorem.** For $\varepsilon,\tau>0$ (and strong initial data with $\|\varphi_0\|_\infty<\ell$):

- the identification problem has a minimizer;
- the control-to-state map $(P,\chi,\eta,C)\mapsto(\varphi,\mu,\sigma)$ is Fréchet differentiable, its derivative being the solution of the linearized system;
- every optimal $(\bar P,\bar\chi,\bar\eta,\bar C)$ with state $(\bar\varphi,\bar\mu,\bar\sigma)$ and adjoint state $(p,q,r)$ satisfies the variational inequality

$$ \int_Q(P-\bar P)\bar\sigma f(\bar\varphi)p+\int_Q(\chi-\bar\chi)\bar\sigma q-\int_Q(\eta-\bar\eta)\Delta\bar\varphi\,r-\int_Q(C-\bar C)\bar\sigma f(\bar\varphi)r+\alpha_P(\bar P-P_*)(P-\bar P)+\alpha_\chi(\bar\chi-\chi_*)(\chi-\bar\chi)+\alpha_\eta(\bar\eta-\eta_*)(\eta-\bar\eta)+\alpha_C(\bar C-C_*)(C-\bar C)\ge0 $$

for all $(P,\chi,\eta,C)\in\mathcal U_{ad}$.

Moreover, the identification problems are stable under removing the regularizations: as $\varepsilon\to0$, $\tau\to0$, or $(\varepsilon,\tau)\to(0,0)$ (with $\eta=0$ in the limits that require it), minimizers of the limiting problems exist, every optimal control of a limiting problem is the limit of optimal controls of suitably adapted regularized problems (with convergence of the corresponding states), and the first-order condition passes to the limit.

## Expansion

Existence follows from compactness of the finite-dimensional control box together with continuous dependence of strong solutions on the parameters, which rests on the separation property $\sup_t\|\varphi(t)\|_\infty\le r^*<\ell$ keeping $F$ and its derivatives bounded along trajectories. Differentiability comes from well-posedness of the linearized system and an estimate of the second-order remainder. Introducing the adjoint backward system turns the derivative of $\mathcal J$ in a direction $h$ into explicit integrals against $(p,q,r)$, giving the stated inequality. The asymptotic results use the adapted-functional technique: add $\tfrac12|u-\bar u_0|^2$ penalties towards a fixed optimal control of the limit problem, derive estimates on states and adjoints uniform in $\varepsilon$ or $\tau$, and pass to the limit in state, adjoint and optimality systems.

## Sources

- E. Rocca, L. Scarpa and A. Signori, "Parameter identification for nonlocal phase field models for tumor growth via optimal control and asymptotic analysis", arXiv:2009.11159 (2020), <https://doi.org/10.48550/arXiv.2009.11159>. Theorem 3.1 (existence of a minimizer), Theorem 3.3 (Fréchet differentiability), Theorem 3.6 (first-order optimality conditions), Theorems 4.1, 4.4 and 4.6 ($\varepsilon\to0$), Theorems 4.7 and 4.10 ($\tau\to0$) and the subsection on $(\overline{CP})$ for $(\varepsilon,\tau)\to(0,0)$; the state system and cost functional are in Section 1 and the assumptions in Section 2. Published version: Mathematical Models and Methods in Applied Sciences 31 (2021) 2643–2694, <https://doi.org/10.1142/s0218202521500585>.
