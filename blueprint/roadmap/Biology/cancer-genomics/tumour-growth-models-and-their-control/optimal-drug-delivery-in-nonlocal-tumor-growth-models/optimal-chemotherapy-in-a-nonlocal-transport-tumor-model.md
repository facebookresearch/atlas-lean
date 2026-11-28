# Optimal chemotherapy in a nonlocal transport model of solid tumor growth

**Model.** Let $p(t,x)\ge0$ be the tumor cell density and $d(t,x)\ge0$ the drug concentration on $[0,T]\times\mathbb{R}^N$, driven by an infusion rate $I(t)$ from the admissible set

$$U_{ad}=\{u\in L^\infty(0,T):\ 0\le u(t)\le M_{tol}\ \text{a.e.}\}.$$

Cells move with a *nonlocal* velocity depending on the convolution $w_p(t,x)=\int_\Omega K(x,y)\,p(t,y)\,dy$ (long-range cell–cell interaction), proliferate at rate $F(p)$ and are killed at rate $C(d,p)$; the drug diffuses and is supplied through $\Gamma(I,d)$:

$$\partial_t p+\operatorname{div}\bigl(\mathrm V[w_p]\,p\bigr)=F(p)-C(d,p),\qquad \partial_t d-\operatorname{div}\bigl(D(x)\nabla d\bigr)=\Gamma(I(t),d),$$

with $p(0)=p_0$, $d(0)=d_0$. The cost balances cumulative tumor burden, toxicity and final tumor size, with weights $\alpha,\beta,\gamma>0$:

$$J(I)=\int_0^T\Bigl[\alpha\int_{\mathbb{R}^N}p(t,x)\,dx+\beta I(t)^2\Bigr]dt+\gamma\int_{\mathbb{R}^N}p(T,x)\,dx .$$

**Hypotheses.** $D\in C^1_b$ is uniformly elliptic ($0<D_0\le D\le D_1$); $d_0\in H^2\cap L^\infty$, $p_0\in L^\infty\cap W^{1,1}$; $F$, $C$, $\Gamma$ are Lipschitz with linear-growth bounds; $K\in C^2_b\cap L^1$; $\mathrm V\in C^2_b(\mathbb{R};\mathbb{R}^N)$ (assumptions (A1)–(A9)); for the optimality system additionally $F,C,\Gamma\in C^1_b$, $K$ vanishes on $\partial\Omega$ and $\mathrm V(0)=\mathrm V'(0)=0$ ((A10)–(A12)).

**Theorem.**

1. *(Well-posedness.)* For each fixed $I$, the system has a unique solution $(p,d)\in C(0,T;L^1(\mathbb{R}^N))\times C(0,T;H^1(\mathbb{R}^N))$ with $\|p(t)\|_{L^1}\le C_1(\|p_0\|_{L^1}+T)$, $\|p(t)\|_{L^\infty}\le C_2(\|p_0\|_{L^\infty}+T)$ and $\|d\|_{L^\infty L^\infty}\le C_4(1+\|d_0\|_{L^\infty}+\|I\|_{L^\infty})$; nonnegative data give nonnegative $p,d$.
2. *(Existence.)* There is an optimal infusion $I^*\in U_{ad}$ minimizing $J$.
3. *(Optimality.)* The control-to-state map and $J$ are Gâteaux differentiable, and with the adjoint state $(q,r)$ of the linearized system,

$$I^*(t)=\max\Bigl\{0,\ \min\Bigl\{M_{tol},\ -\frac{1}{2\beta}\int_{\mathbb{R}^N}\partial_1\Gamma(I^*,d^*)\,r(t,x)\,dx\Bigr\}\Bigr\}\quad\text{a.e. }t\in[0,T].$$

## Expansion

The drug equation is solved first by the analytic semigroup of the uniformly elliptic operator $-\operatorname{div}(D\nabla\cdot)$ plus Gronwall; with $d$ frozen, the nonlocal balance law is solved along characteristics $\mathrm X[t,x]$ of the velocity $\mathrm V[w_p]$ with a fixed-point argument, the Jacobian $\det D_x\mathrm X=\exp(-\int\operatorname{div}\mathrm V)$ giving the $L^\infty$ bound. Existence of a minimizer follows from weak-$*$ compactness of $U_{ad}$, continuity of the control-to-state map, and convexity of the quadratic toxicity term. The variational inequality $\int_0^T(2\beta I^*+\int\partial_1\Gamma\,r\,dx)(v-I^*)\,dt\ge0$ for all $v\in U_{ad}$ is equivalent to the projection formula in item 3: the dose is the unconstrained stationary point clipped to $[0,M_{tol}]$.

## Sources

- Yassine Melouani, Abderrahman Bouhamidi, Imad El Harraki, "Optimal control of medical drug in a nonlocal model of solid tumor growth", Journal of Mathematical Analysis and Applications 560 (2026), 130573, <https://doi.org/10.1016/j.jmaa.2026.130573>. Published version of arXiv:2503.09208, cited next; locators there refer to the arXiv version.
- A. Bouhamidi, I. El Harraki, Y. Melouani, "Optimal Control of Medical Drug in a Nonlocal Model of Solid Tumor Growth", arXiv:2503.09208 (2025), Section 2 (model, Assumptions (A1)–(A12), cost functional), Theorem 3.1, Lemma 3.1, Theorem 3.2, Theorems 4.1–4.2 and Corollary 4.1. <https://doi.org/10.48550/arXiv.2503.09208>
