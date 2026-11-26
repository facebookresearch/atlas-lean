# Strong well-posedness of cyclic catalytic SPDEs with mutation and immigration

Consider the cyclic catalytic reaction–diffusion system on $I=(0,1)$ with Neumann boundary conditions, Metzler mutation matrix $Q=(q_{ij})$, immigration $\theta\ge0$ and spatially colored noise with covariance diagonal $\lambda_i(x)=\sum_m\sigma_{im}(x)^2$, under the hypotheses and the strict cyclic gap $q_{i,i+1}-\tfrac14\lambda_i\ge\delta_*>0$ stated in [Power entropy and boundary occupation under a cyclic drift–covariance gap](power-entropy-and-boundary-occupation-under-a-cyclic-drift-covariance-gap.md). A weak variational solution is a nonnegative progressively measurable $u\in L^2(\Omega;C([0,T];L^2(I)^K))\cap L^2(\Omega\times[0,T];H^1(I)^K)$ satisfying the equation tested against every $\varphi\in H^1(I)$; two solutions are synchronized if they live on the same stochastic basis and are driven by the same Wiener processes.

**Hellinger stability.** Let $h(r,s)=(\sqrt r-\sqrt s)^2$ and $\mathcal H(u,v)=\sum_{i=1}^K\int_I h(u_i(x),v_i(x))\,dx$. For any two synchronized nonnegative weak variational solutions $u,v$,

$$
\mathbb{E}\,\mathcal H(u(t),v(t))\le e^{q_{\mathrm H}t}\,\mathbb{E}\,\mathcal H(u(0),v(0)),\qquad 0\le t\le T,
$$

where $q_{\mathrm H}=\max_j\big\|2q_{jj}^++\sum_{i\ne j}q_{ij}\big\|_{L^\infty(I)}$. In particular, pathwise uniqueness holds.

**Strong well-posedness.** The system has a unique nonnegative probabilistically strong weak variational solution driven by the prescribed cylindrical Wiener process. It satisfies the mild formulation, has a version in $C([0,T];C(\bar I)^K)$ for every $T>0$, and for every $T>0$, $q\ge1$,

$$
\mathbb{E}\sup_{t\le T}\|u(t)\|_{L^2(I)^K}^{2q}+\mathbb{E}\Big(\int_0^T\|u(t)\|_{H^1(I)^K}^2\,dt\Big)^q\le C_{q,T}\big(1+\|u_0\|_{L^2(I)^K}^{2q}\big).
$$

Unlike the spaceless cyclic system $dX_i=\alpha_iX_i\,dt+\sqrt{\gamma_iX_iX_{i+1}}\,dB_i$, where a coordinate hitting zero stays there, mutation and immigration push vanishing coordinates back inside, so boundary-trapping arguments are unavailable; the strict gap replaces them.

## Depends on

- [Power entropy and boundary occupation under a cyclic drift–covariance gap](power-entropy-and-boundary-occupation-under-a-cyclic-drift-covariance-gap.md)

## Expansion

*Stability.* Apply a two-component variational Itô formula to a regularized Hellinger integrand $h_\eta$. Its Hessian is positive semidefinite of rank one, so the Neumann heat term is dissipative. Off-diagonal mutation enters through the perspective identity $c\,\partial_x h_\eta+d\,\partial_y h_\eta\le h(c,d)$, the diagonal growth is bounded by $2h_\eta$, and immigration contracts. For the catalytic noise the drift and the Itô trace combine into $a\,h(c,d)-a|U-V|^2+\tfrac{\lambda}{4}|\alpha U-\beta V|^2$; the gap $a-\lambda/4\ge\delta_*$ absorbs the last term up to a boundary error of size $\eta^{1/2-p}$ times the power-entropy weights, which stay bounded by the boundary-occupation theorem. Letting $\eta\to0$ and applying Gronwall's inequality gives the bound.

*Existence.* Smooth the square root near zero by $g_n(r)=r/\sqrt{r+\varepsilon_n}$, truncate amplitudes and noise modes to get globally Lipschitz, positivity-preserving equations, and prove energy, mass, time-increment and spatial-continuity bounds uniform in the regularization. The joint laws of the approximations and the driving noise are tight; every limit is identified as a weak solution through its martingales, brackets and cross-variations; pathwise uniqueness plus the Gyöngy–Krylov criterion upgrade convergence in law to convergence in probability on the original basis, giving a strong solution.

## Sources

- Jie Xiong and Wen Xu, *Strong well-posedness for cyclic catalytic reaction–diffusion SPDEs with mutation and immigration*, arXiv:2610.41400 (2026), Theorems 2.7 and 2.8, Definitions 2.3–2.4, Sections 3–6. <https://doi.org/10.48550/arXiv.2610.41400>
