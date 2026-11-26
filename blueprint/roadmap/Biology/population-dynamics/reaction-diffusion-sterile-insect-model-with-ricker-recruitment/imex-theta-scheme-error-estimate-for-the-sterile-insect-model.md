# IMEX $\theta$-scheme error estimate for the sterile insect model

**Setting.** Consider the reaction–diffusion SIT model for wild males $M$, wild females $F$ and sterile males $M_S$ on a bounded domain $\Omega$ with Neumann conditions, whose nonlinear recruitment is $r\rho G(X)$ and $(1-r)\rho G(X)$ with $G(X)=\frac{FM}{M+\gamma M_S}e^{-\sigma(M+F)}$, $X=(M,F,M_S)$. On an equidistant grid $t_m=m\,\delta t$ of $I=[0,T]$, treat the nonlinear recruitment explicitly and diffusion and linear mortality implicitly with a one-step-$\theta$ rule, $\theta\in[\tfrac12,1]$. In weak form: for all test functions $\varphi\in H^1(\Omega)$,

$$\Big(\tfrac{M^m-M^{m-1}}{\delta t},\varphi\Big)+\alpha_M\big(\nabla M^{m,\theta},\nabla\varphi\big)+\mu_M\big(M^{m,\theta},\varphi\big)=r\rho\,\big(G(X^{m-1}),\varphi\big),$$

where $M^{m,\theta}=\theta M^m+(1-\theta)M^{m-1}$, with the analogous equations for $F$ (factor $1-r$) and for $M_S$ (right side $(\Lambda,\varphi)$, no recruitment). Each step requires only a linear elliptic solve. Let $\|X\|_\Omega$ be the $L^2(\Omega)$ norm of the triple and

$$\|X\|_*^2=\mu_M\|M\|^2+\alpha_M\|\nabla M\|^2+\mu_F\|F\|^2+\alpha_F\|\nabla F\|^2+\mu_S\|M_S\|^2+\alpha_S\|\nabla M_S\|^2$$

the energy norm of the linear part.

**Theorem.** Assume the exact solution lies in $W^{1,\infty}(I;H^1(\Omega))\cap W^{2,\infty}(I;L^2(\Omega))$ and set $\delta_{\min}=\min_{\Omega\times I}(M+\gamma M_S)>0$. Then the error $e^X_n=X(t_n)-X^n$ satisfies, for $n\le N$ and a constant $c>0$,

$$\|e^X_n\|_\Omega^2+\frac{(1-\theta)^2}{\theta}\,\delta t\,\|e^X_n\|_*^2+\delta t\sum_{m=1}^{n}\Big(\frac{\|e^X_m-e^X_{m-1}\|_\Omega^2}{\delta t}+\Big(2-\frac1\theta\Big)\|e^X_m\|_*^2+\theta\Big\|e^X_m+\frac{1-\theta}{\theta}e^X_{m-1}\Big\|_*^2\Big)$$

$$\le c\,e^{c_\delta T}\,\delta t^2\Big(\|\partial_tX\|^2_{L^\infty(0,t_n;H^1)}+\|\partial_t^2X\|^2_{L^\infty(0,t_n;L^2)}\Big),\qquad c_\delta=\frac{\rho^2}{\delta_{\min}^2}\,\|L(X)\|^2_{L^\infty((0,t_n)\times\Omega)},$$

where $L(X)=\sigma FM+F+\gamma^2(F+M_S)+1$ is the local Lipschitz factor of $G$.

In particular each population converges at first order, $\|M(t_m)-M^m\|_\Omega+\|F(t_m)-F^m\|_\Omega+\|M_S(t_m)-M_S^m\|_\Omega=\mathcal{O}(\delta t)$. The sum on the left acts as numerical diffusion added by the time discretization, and it grows with $\theta$.

## Expansion

Subtract the scheme from the exact equations at $t_m$ to get an error equation driven by consistency residuals (Taylor remainders of order $\delta t$ in $\partial_tX$ and $\partial_t^2X$) plus the explicit-reaction defect $\rho\,(G(X(t_m))-G(X^{m-1}))$. Testing with $e^X_m$ and using the algebraic identity for $\theta$-averages produces the telescoping $L^2$ terms and the energy-norm terms on the left. The reaction defect is bounded via the Lipschitz estimate $|G(X)-G(\hat X)|\le L(X)|X-\hat X|/(M+\gamma M_S)$, which needs the denominator bounded below by $\delta_{\min}$ (guaranteed by the positivity of sterile males). Young's inequality and a discrete Gronwall lemma then give the exponential factor $e^{c_\delta T}$.

## Depends on

- [Well-posedness of the reaction–diffusion sterile insect model](well-posedness-of-the-reaction-diffusion-sterile-insect-model.md)

## Sources

- Oscar Eduardo Escobar-Lasso, Stefan Frei, Reinhard Racke, Olga Vasilieva, "Analysis and numerical simulation of a spatio-temporal Ricker-type model for the control of Aedes aegypti mosquitoes with Sterile Insect Techniques", arXiv:2603.24460 (2026): time-discrete scheme in Section 4.1, Theorem 2 (temporal error estimate), Remark 1 (first-order convergence and numerical diffusion). <https://doi.org/10.48550/arXiv.2603.24460>
