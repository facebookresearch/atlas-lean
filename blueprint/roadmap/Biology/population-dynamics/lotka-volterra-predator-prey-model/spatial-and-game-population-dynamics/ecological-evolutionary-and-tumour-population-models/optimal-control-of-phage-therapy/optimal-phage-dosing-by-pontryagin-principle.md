# Optimal phage dosing by Pontryagin's principle

For the scaled [phage therapy model](phage-therapy-model-with-resistance-and-innate-immunity.md) $\dot x=f(x,u)$, $x(0)=x_0$, on $[t_0,t_f]$, with admissible controls the measurable $u:[t_0,t_f]\to U=\{u\in\mathbb{R}_+^2:\|u\|_1\le1\}$, minimize the Bolza cost

$$J(u)=\int_{t_0}^{t_f}\Bigl[\theta_B(x_1+x_2)+\frac{\theta_u}2\|u\|_2^2\Bigr]dt+\theta_f\bigl(x_1(t_f)+x_2(t_f)\bigr),\qquad\theta_B,\theta_u,\theta_f>0.$$

**Existence.** An optimal control exists, because the dynamics are affine in $u$, $U$ is compact and convex, the running cost is convex in $u$, the terminal cost is continuous, and trajectories stay in a bounded invariant set (Fleming–Rishel existence theorem).

**Necessary conditions.** If $u^*$ is optimal with state $x^*$, let $\lambda^*$ solve the costate problem

$$\dot\lambda^*=-\Bigl(\frac{\partial f}{\partial x}(x^*)\Bigr)^{\!\top}\lambda^*-(\theta_B,\theta_B,0,0,0)^\top,\qquad \lambda^*(t_f)=(\theta_f,\theta_f,0,0,0)^\top .$$

Then for almost every $t$,

$$u^*(t)=P_U\bigl(\hat u(t)\bigr),\qquad \hat u(t)=-\frac q{\theta_u}\begin{pmatrix}\lambda_3^*(t)\\ \lambda_5^*(t)\end{pmatrix},$$

where $P_U$ is the Euclidean projection onto $U$.

## Depends on

- [Phage therapy model with resistance and innate immunity](phage-therapy-model-with-resistance-and-innate-immunity.md)

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

The Hamiltonian $H=\lambda^\top f(x,u)+\theta_B(x_1+x_2)+\frac{\theta_u}2\|u\|_2^2$ depends on $u$ only through $q\lambda_3u_1+q\lambda_5u_2+\frac{\theta_u}2\|u\|^2$, because the controls enter only the phage equations, additively. Pontryagin's principle requires $u^*(t)$ to minimize $H$ over $U$; completing the square, this is minimizing $\frac{\theta_u}2\|u-\hat u\|^2$ over the convex set $U$, whose unique solution is the projection $P_U(\hat u)$. A negative costate $\lambda_3^*$ (more sensitive-targeting phage lowers future cost) therefore turns on $u_1$, and the simplex constraint forces trade-offs between the two phages when both are wanted. The source computes the optimal schedules by a projected gradient method.

## Sources

- G. Li, C. Y. Leung, Y. Wardi et al., *Optimizing the timing and composition of therapeutic phage cocktails: a control-theoretic approach*, Bulletin of Mathematical Biology 82 (2020), article 75, <https://doi.org/10.1007/s11538-020-00751-w> (PMCID: PMC8272981). Section 2.2, equations (14)–(16); Section 3.1, existence of optimal control via Fleming and Rishel (Theorem 4.1 there); Section 3.2, Theorem 1, equations (17)–(23), and Appendix A (projection onto $U$).
