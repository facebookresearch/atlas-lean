# Sparse optimal control of a phase-field tumour model with hyperbolic relaxation of the chemical potential

**State system.** On a smooth bounded domain $\Omega\subset\mathbb R^3$, with $Q=\Omega\times(0,T)$ and fixed relaxation parameters $\alpha,\tau>0$, the chemical potential $\mu$, tumour phase field $\varphi$ and nutrient $\sigma$ solve

$$\begin{aligned} \alpha\,\partial_{tt}\mu+\partial_t\varphi-\Delta\mu&=P(\varphi)\big(\sigma+\chi(1-\varphi)-\mu\big)-h(\varphi)\,u_1,\\ \tau\,\partial_t\varphi-\Delta\varphi+F'(\varphi)&=\mu+\chi\sigma,\\ \partial_t\sigma-\Delta\sigma&=-\chi\Delta\varphi-P(\varphi)\big(\sigma+\chi(1-\varphi)-\mu\big)+u_2, \end{aligned}$$

with homogeneous Neumann conditions and initial data $\mu(0),\partial_t\mu(0),\varphi(0),\sigma(0)$. Here $P\ge0$ is a proliferation function, $\chi\ge0$ the chemotaxis coefficient, $F$ a double-well potential (regular, or singular such as logarithmic on $(r_-,r_+)$), $u_1$ a drug distribution acting through $h(\varphi)$ and $u_2$ a nutrient supply.

**Theorem (well-posedness and separation).** For $\mu_0\in H^1$, $\mu_0'\in L^2$, $\sigma_0\in H^1$, $\varphi_0\in H^2$ with $r_-<\varphi_0<r_+$ on $\overline\Omega$, and $\mathbf u\in L^\infty(Q)\times L^2(Q)$, the system has a unique solution, bounded in norm by a constant depending only on $\|\mathbf u\|$, and depending Lipschitz-continuously on $\mathbf u$ in $L^2$. Under slightly stronger data and $\mathbf u\in L^2(0,T;H^1)\times L^\infty(0,T;L^2)$, one has $\sigma\in L^\infty(Q)$, $F'(\varphi)\in L^\infty(Q)$ and the **separation property** $r_-<r_*\le\varphi\le r^*<r_+$ on $\overline Q$.

**Control problem.** Minimize

$$\mathcal J=\frac{b_1}{2}\int_Q|\varphi-\widehat\varphi_Q|^2+\frac{b_2}{2}\int_\Omega|\varphi(T)-\widehat\varphi_\Omega|^2+\frac{b_3}{2}\int_Q|\mathbf u|^2+\kappa\,\mathcal G(\mathbf u)$$

over box constraints $\underline u_i\le u_i\le\widehat u_i$, where $\mathcal G$ is convex, continuous and nondifferentiable, e.g. $\mathcal G(\mathbf u)=\|u_1\|_{L^1(Q)}+\|u_2\|_{L^1(Q)}$.

**Theorem (existence and first-order conditions).** An optimal control exists. If $\bar{\mathbf u}$ is locally optimal, there are an adjoint state $(p,q,r)$ and $\bar\lambda\in\partial\mathcal G(\bar{\mathbf u})$ such that the variational inequality $D\widetilde J(\bar{\mathbf u})[\mathbf u-\bar{\mathbf u}]+\kappa\int_Q\bar\lambda\cdot(\mathbf u-\bar{\mathbf u})\ge0$ holds for all admissible $\mathbf u$, equivalently

$$\bar u_1=\max\Big\{\underline u_1,\min\Big\{\widehat u_1,-b_3^{-1}\big(-h(\bar\varphi)p+\kappa\bar\lambda_1\big)\Big\}\Big\},\qquad \bar u_2=\max\Big\{\underline u_2,\min\Big\{\widehat u_2,-b_3^{-1}\big(r+\kappa\bar\lambda_2\big)\Big\}\Big\}.$$

The same conclusions hold for singular potentials via the separation property.

**Theorem (full sparsity).** For $\mathcal G=\|\cdot\|_{L^1}$ summed over components and constant thresholds $\underline u_i<0<\widehat u_i$, every locally optimal control satisfies, for a.e. $(x,t)\in Q$,

$$\bar u_1(x,t)=0\iff|h(\bar\varphi(x,t))\,p(x,t)|\le\kappa,\qquad \bar u_2(x,t)=0\iff|r(x,t)|\le\kappa .$$

So the drug and nutrient controls switch off exactly where the corresponding adjoint signal is below the sparsity weight $\kappa$.

## Expansion

The hyperbolic term $\alpha\partial_{tt}\mu$ makes the first equation a damped wave equation, so energy estimates are carried out on $1*\mu$ (time integral) as well as on $\mu$; the viscous term $\tau\partial_t\varphi$ gives $L^\infty$ bounds that, with the singular potential, keep $\varphi$ uniformly away from the pure phases. Fréchet differentiability of the control-to-state map follows from the linearized system, and the subdifferential calculus for convex $\mathcal G$ yields the variational inequality. Since $\partial|u|$ is $\{\pm1\}$ off zero and $[-1,1]$ at zero, inserting it in the projection formula gives the sparsity equivalences.

## Sources

- Pierluigi Colli, Elisabetta Rocca, Jürgen Sprekels, "Optimal control of a tumor growth model with hyperbolic relaxation of the chemical potential", arXiv:2603.14960 (2026): problem (CP) and state system, Theorems 2.2 and 2.3, Lemma 3.1 and the projection formulas of Section 3, Section 4 (singular potentials), Theorem on full sparsity in Section 5. <https://doi.org/10.48550/arXiv.2603.14960>
