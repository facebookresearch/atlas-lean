# Power entropy and boundary occupation under a cyclic drift–covariance gap

Let $I=(0,1)$, $K\ge 2$, and consider the cyclic catalytic stochastic reaction–diffusion system, with the convention $u_{K+1}=u_1$,

$$
du_i(t,x)=\Big[\tfrac12\Delta_N u_i+\sum_{j=1}^K q_{ij}(x)u_j+\theta_i(x)\Big]dt+\sqrt{u_i u_{i+1}}\sum_{m\ge1}\sigma_{im}(x)\,d\beta_{im}(t),\qquad i=1,\dots,K,
$$

where $\Delta_N$ is the Neumann Laplacian, the $\beta_{im}$ are independent Brownian motions, and

- $Q=(q_{ij})$ is a Metzler matrix of bounded measurable functions: $q_{ij}\ge 0$ for $i\ne j$ (mutation rates); diagonal entries of either sign are allowed;
- $\theta_i\in L^\infty(I)$, $\theta_i\ge0$ (immigration);
- $\sum_m\|\sigma_{im}\|_{L^\infty}^2<\infty$, with covariance diagonal $\lambda_i(x)=\sum_m\sigma_{im}(x)^2$;
- $u_0\in H^1(I)^K$ is nonnegative.

**Strict cyclic gap.** Assume there is $\delta_*>0$ with

$$
q_{i,i+1}(x)-\tfrac14\lambda_i(x)\ge\delta_*\qquad\text{for all } i \text{ and a.e. } x\in I .
$$

Write $\mathcal R_i(z)=\sum_{j\ne i,\,i+1}q_{ij}z_j$ for the off-cycle incoming mutation.

**Theorem.** There exists $p\in(0,1/2)$ such that, for every $T>0$, every nonnegative weak variational solution $u$, every $0<\eta\le1$ and every $i$,

$$
\mathbb{E}\int_0^T\!\!\int_I\frac{|\partial_x u_i|^2}{(u_i+\eta)^{2-p}}\,dx\,dt+\mathbb{E}\int_0^T\!\!\int_I\frac{u_{i+1}+\mathcal R_i(u)+\theta_i}{(u_i+\eta)^{1-p}}\,dx\,dt\le C_T,
$$

with $C_T$ independent of $\eta$. Consequently, for $0<r\le1$,

$$
\mathbb{E}\int_0^T\!\!\int_I\big(u_{i+1}+\mathcal R_i(u)+\theta_i\big)\mathbf 1_{\{u_i\le r\}}\,dx\,dt\le C_T r^{1-p},\qquad \mathbb{E}\int_0^T\!\!\int_I|\partial_x u_i|^2\mathbf 1_{\{u_i\le r\}}\,dx\,dt\le C_T r^{2-p}.
$$

So the catalyst mass, the incoming mutation and immigration, and the heat energy spent near the face $\{u_i=0\}$ all vanish at an explicit polynomial rate in the width $r$ of the boundary layer.

## Expansion

Apply Itô's formula to the concave functional $\Phi(u_i)=\int_I (u_i+\eta)^p\,dx$. The Neumann heat term contributes $\tfrac12 p(1-p)\int_I(u_i+\eta)^{p-2}|\partial_x u_i|^2\,dx\ge0$, the inward cyclic drift contributes $p\,q_{i,i+1}u_{i+1}(u_i+\eta)^{p-1}$, and the Itô correction from the catalytic noise is $-\tfrac12 p(1-p)\lambda_i u_iu_{i+1}(u_i+\eta)^{p-2}\ge-\tfrac12 p(1-p)\lambda_i u_{i+1}(u_i+\eta)^{p-1}$. Choosing $p=\tfrac12-\rho$ with $\rho\Lambda\le\delta_*$, where $\Lambda=\max_i\|\lambda_i\|_\infty$, gives

$$
q_{i,i+1}-\tfrac{1-p}{2}\lambda_i=q_{i,i+1}-\tfrac14\lambda_i-\tfrac{\rho}{2}\lambda_i\ge\tfrac{\delta_*}{2},
$$

so the catalyst term is a positive entropy production; the other off-diagonal mutation and immigration terms are nonnegative productions as well. Since $\Phi$ is bounded by the mass and energy estimates, all productions have expectation bounded uniformly in $\eta$ (first for smoothed approximations, then for every weak solution). The occupation bounds follow by taking $\eta=r$, because $(u_i+r)^{1-p}\le(2r)^{1-p}$ on $\{u_i\le r\}$. These estimates control the boundary error in the Hellinger stability argument for pathwise uniqueness.

## Sources

- Jie Xiong and Wen Xu, *Strong well-posedness for cyclic catalytic reaction–diffusion SPDEs with mutation and immigration*, arXiv:2610.41400 (2026), Theorem 2.6, Proposition 4.5 and Corollary 4.6; standing hypotheses in Assumptions 2.1 and 2.2. <https://doi.org/10.48550/arXiv.2610.41400>
