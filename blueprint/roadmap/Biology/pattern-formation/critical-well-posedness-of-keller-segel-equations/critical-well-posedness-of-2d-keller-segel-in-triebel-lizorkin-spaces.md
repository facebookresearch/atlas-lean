# Critical well-posedness of the 2D Keller–Segel equation in Triebel–Lizorkin spaces

**Setting.** The two-dimensional parabolic–elliptic Keller–Segel equation for a cell density $u$ is

$$\partial_tu-\Delta u+\nabla\cdot\big(u\nabla(-\Delta)^{-1}u\big)=0,\qquad u|_{t=0}=u_0,\qquad x\in\mathbb R^2.$$

It is invariant under $u_\lambda(t,x)=\lambda^2u(\lambda^2t,\lambda x)$, which leaves $L^1(\mathbb R^2)$, and more generally the homogeneous Triebel–Lizorkin spaces $\dot F^0_{1,q}(\mathbb R^2)$, scale-invariant.

**Obstruction.** For $q>2$ and $T>0$ there is no constant $C$ with $\|e^{t\Delta}u_0\|_{L^2(0,T;\dot F^1_{1,q})}\le C\|u_0\|_{\dot F^0_{1,q}}$, so the usual Bochner-space heat smoothing fails at this endpoint. In *time-refined* spaces $\dot F^s_{1,q}(L^r_T)$, where the $L^r$ time norm is taken for each dyadic block before the $\ell^q$ summation, the heat flow does smooth: for $1\le a\le r\le\infty$ and $\sigma=2(1+\tfrac1r-\tfrac1a)$, the solution of $\partial_tu-\Delta u=F$ satisfies

$$\|u\|_{\dot F^{s+\sigma}_{1,q}(L^r_T)}\lesssim\|u_0\|_{\dot F^{s+2-2/a}_{1,q}}+\|F\|_{\dot F^s_{1,q}(L^a_T)},$$

and the Keller–Segel drift obeys the endpoint bilinear estimate (for $2\le q<\infty$)

$$\big\|\nabla\cdot\big(f\nabla(-\Delta)^{-1}g\big)\big\|_{\dot F^0_{1,q}(L^1_T)}\lesssim\|f\|_{\dot F^1_{1,q}(L^2_T)}\|g\|_{\dot F^1_{1,q}(L^2_T)}.$$

**Theorem.** Let $2\le q<\infty$ and $u_0\in\dot F^0_{1,q}(\mathbb R^2)$. There is $T>0$ such that the Keller–Segel equation has a unique mild solution in the time-refined class $X^q_T$, with $u\in C([0,T];\dot F^0_{1,q})$ and continuous dependence on the data. There is $\varepsilon_q>0$ such that if $\|u_0\|_{\dot F^0_{1,q}}\le\varepsilon_q$ the solution is global. The same holds for the two-component drift–diffusion system treated in the same framework.

## Expansion

Duhamel's formula writes the solution as $e^{t\Delta}u_0$ minus the heat potential of the drift $\nabla\cdot(u\nabla(-\Delta)^{-1}u)$. The time-refined heat estimate with $(a,r)=(1,2)$ maps the drift from $\dot F^0_{1,q}(L^1_T)$ into $\dot F^1_{1,q}(L^2_T)$, and the bilinear estimate maps $\dot F^1_{1,q}(L^2_T)\times\dot F^1_{1,q}(L^2_T)$ back into $\dot F^0_{1,q}(L^1_T)$, so a contraction closes in $X^q_T$. Large data are handled by taking $T$ small, since the linear part's time-refined norm tends to $0$ as $T\to0$; small data give a global contraction. The proof of the bilinear estimate uses vector-valued Peetre maximal functions and a Jawerth-type embedding at the $L^1$ endpoint.

## Sources

- Wenhai Shan, Xiao-Song Yang, "Time-refined Triebel–Lizorkin Estimates and Applications to Keller–Segel Type Equations", arXiv:2607.24089 (2026), Proposition 1.1, Theorem 1.2, Proposition 1.3, Theorem 1.4 and Corollary 1.5, <https://doi.org/10.48550/arXiv.2607.24089>.
