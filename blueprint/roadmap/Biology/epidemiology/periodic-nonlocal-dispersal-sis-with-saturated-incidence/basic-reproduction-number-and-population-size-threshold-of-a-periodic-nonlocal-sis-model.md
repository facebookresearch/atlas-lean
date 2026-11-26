# Basic reproduction number and population-size threshold of a periodic nonlocal-dispersal SIS model with saturated incidence

**Model.** On a bounded smooth domain $\Omega\subset\mathbb{R}^n$ with total population $N=\int_\Omega(S+I)$,
$$\begin{aligned}S_t&=d_S\!\int_\Omega J(x-y,t)\,[S(y,t)-S(x,t)]\,dy-\frac{\beta SI}{m+S+I}+\gamma I,\\ I_t&=d_I\!\int_\Omega J(x-y,t)\,[I(y,t)-I(x,t)]\,dy+\frac{\beta SI}{m+S+I}-\gamma I,\end{aligned}$$
with $T$-periodic positive coefficients $\beta(x,t)$ (transmission), $\gamma(x,t)$ (recovery), saturation parameter $m(x,t)\ge0$ and a nonnegative continuous dispersal kernel $J$; integrating only over $\Omega$ is the nonlocal analogue of a Neumann condition. The unique disease-free equilibrium is $(N/|\Omega|,0)$. Linearizing there gives the effective transmission rate
$$\theta(x,t)=\frac{\beta(x,t)\,N/|\Omega|}{m(x,t)+N/|\Omega|},$$
and $R_0=R_0(d_I,N,m)$ is the spectral radius of the next-generation operator of the periodic problem $\partial_t\varphi=d_I\mathcal{J}[\varphi]-\gamma\varphi+\theta\varphi$.

**Theorem.**
1. *(Variational formula.)* $R_0=\inf_{\varphi}\sup_{(x,t)}\dfrac{\theta\varphi}{\partial_t\varphi-d_I\mathcal{J}[\varphi]+\gamma\varphi}$ over positive Lipschitz $T$-periodic $\varphi$ with $-\partial_t\varphi+d_I\mathcal{J}[\varphi]-\gamma\varphi<0$, with a matching sup–inf formula.
2. *(Bounds.)* $\dfrac{\iint\theta}{\iint\gamma}\le R_0\le\max_{x(\cdot)\ T\text{-periodic}}\dfrac{\int_0^T\theta(x(t),t)\,dt}{\int_0^T\gamma(x(t),t)\,dt}$; for fixed $d_I$ and $m>0$, $R_0$ is strictly increasing in $N$.
3. *(Population-size threshold.)* Let $H^\pm=\{x:\overline\beta(x)\gtrless\overline\gamma(x)\}$ with $\overline{\,\cdot\,}$ the time average. If $H^-=\Omega$, then $R_0<1$ for all small $d_I$, all $N$ and all $m$. If $H^+\ne\emptyset$, then for small $d_I$ and $m>0$ there is $N^*(d_I,m)$ with $R_0<1$ for $N<N^*$, $R_0=1$ at $N^*$, and $R_0>1$ for $N>N^*$ (for every $d_I$ when $H^+=\Omega$).
4. *(Threshold dynamics.)* If $\beta\le\gamma$ everywhere, the disease-free equilibrium is globally attractive. When $d_S=d_I=d$: if $R_0\le1$ the disease-free equilibrium is globally attractive; if $R_0>1$ there is a unique positive periodic endemic solution, and it is globally attractive.
5. *(Limits.)* As $\|m\|\to0$ (and $\iint\beta>\iint\gamma$), the endemic state converges to that of the standard-incidence problem; as $d\to0$ or $d\to\infty$ it converges to explicit periodic limits.

## Expansion

With saturation $m>0$ the per-contact force of infection at the disease-free state is $\beta\,\bar s/(m+\bar s)$ with $\bar s=N/|\Omega|$, so crowding raises transmission. This is why $R_0$ depends on $N$, unlike under standard incidence, and why a larger population can push $R_0$ across $1$ at a critical size $N^*$. Monotonicity in $N$ follows from the variational formula because $\theta$ is increasing in $N$. Equal dispersal rates make $S+I$ satisfy a linear nonlocal equation converging to $N/|\Omega|$, which reduces the system to a scalar periodic equation for $I$ with a comparison principle, giving uniqueness and global attractivity.

## Sources

- Ziwei Liang, Xiandong Lin and Qiru Wang, "Threshold dynamics of a time-periodic nonlocal dispersal SIS epidemic model with saturated incidence function and Neumann boundary conditions", arXiv:2608.21907 (2026), Theorem 2.1, Corollaries 2.1–2.2, Theorems 3.1–3.4 and Section 4, <https://doi.org/10.48550/arXiv.2608.21907>.
