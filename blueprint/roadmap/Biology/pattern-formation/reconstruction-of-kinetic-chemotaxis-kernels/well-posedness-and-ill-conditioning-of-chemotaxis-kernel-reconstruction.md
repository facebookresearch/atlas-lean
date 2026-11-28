# Well-posedness and ill-conditioning of chemotaxis kernel reconstruction

**Forward model.** In one space dimension with velocities $V=\{\pm1\}$, the bacterial phase-space density $f(t,x,v)$ solves the run-and-tumble equation

$$\partial_t f+v\,\partial_x f=\int_V\bigl(K(x,v,v')f(t,x,v')-K(x,v',v)f(t,x,v)\bigr)\,dv',\qquad f(0,x,v)=\phi(x,v),$$

with tumbling kernel $K\ge0$, bounded by $C_K$, piecewise constant in $x$ on intervals $I_r=[a_{r-1},a_r)$, $r=1,\dots,R$. **Data**: for test functions $\mu_l$ and a time $T$, $M_l(K)=\int_{\mathbb{R}}\int_V f_K(x,T,v)\,dv\,\mu_l(x)\,dx$, $l=1,\dots,L$ (the macroscopic density only). **Inverse problem**:

$$\min_K\ \mathcal{C}(K)=\frac{1}{2L}\sum_{l=1}^L\bigl(M_l(K)-y_l\bigr)^2 .$$

**Theorem (local well-posedness).** If the Hessian $H_K\mathcal{C}(K_\star)$ is positive definite at the true kernel $K_\star$ and the measurement Hessians are uniformly bounded in Frobenius norm near $K_\star$, then $H_K\mathcal{C}$ stays positive definite on an $L^\infty$-neighborhood $U$ of $K_\star$, with $|\lambda_{\min}(H_K\mathcal{C}(K_\star))-\lambda_{\min}(H_K\mathcal{C}(K))|\le C'\|K_\star-K\|_\infty$; the problem is Tikhonov well-posed on $U$ and gradient descent started in $U$ converges.

**Theorem (ill-conditioning).** With $L=2R$ measurements, if the test function of one measurement converges to that of another (strongly in $L^1$, or weakly in $L^1$ provided $e^{T|V|C_K}<2$), then an eigenvalue of $H_K\mathcal{C}(K_\star)$ tends to $0$: strong convexity is lost and gradient descent slows down. Redundant, overlapping measurements make reconstruction ill-posed.

**Theorem (decoupling design).** Use an initial condition $\phi=\sum_r\phi_r$ with $\phi_r$ positive, symmetric and decreasing around the interval center $a_{r-1/2}$, supported in $a_{r-1/2}+[-d,d]$; two indicator test functions per interval centered at $a_{r-1/2}\pm T$ of half-width $d_\mu\le d$; and a short measurement time $T<\min\bigl((1-\delta)\tfrac{0.09}{C_K|V|},\ \min_r(\tfrac{a_r-a_{r-1}}{4}-\tfrac d2)\bigr)$ with $\delta=(d+d_\mu)/T<e^{-TC_K|V|}$. Then the Hessian is block diagonal with one $2\times2$ block per interval, each block is positive definite at $K_\star$, and, provided the measurement Hessians $H_KM_l(K)$ are bounded in Frobenius norm in a neighborhood of $K_\star$, the optimization problem is locally well-posed (Theorem 4.2); the reconstruction splits into $R$ independent two-parameter cell problems.

## Expansion

For short times a bump released at the interval center travels left and right at unit speed, and measurements at $a_{r-1/2}\pm T$ mainly see particles that tumbled $0$ or $1$ times; to first order the right-moving mass at $a_{r-1/2}+T$ is governed by $K_r(-,+)$ and the left-moving mass by $K_r(+,-)$, so each pair of measurements identifies the two values of $K$ on its own interval. Choosing $T$ small relative to interval lengths keeps information from different intervals separate, giving the block structure; the time bound with constant $0.09$ controls higher-order tumbling contributions so that each $2\times2$ block is diagonally dominant. When two test functions coincide, the corresponding gradients of $M_l$ coincide and the Gauss–Newton part of the Hessian loses rank.

## Sources

- K. Hellmuth, C. Klingenberg, Q. Li, M. Tang, "Reconstructing the kinetic chemotaxis kernel using macroscopic data: well-posedness and ill-posedness", arXiv:2309.05004 (2023), Section 2 (forward model, measurements and loss), Proposition 3.1, Theorems 3.2–3.3, Propositions 3.2–3.3, Design (D), Proposition 4.1, Theorem 4.2 and Proposition 4.2, <https://doi.org/10.48550/arXiv.2309.05004>.
