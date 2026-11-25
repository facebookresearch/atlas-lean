# Dyadic quadratic variation of bounded continuous martingales

Let $(\Omega,\mathcal A,P)$ carry a filtration satisfying the usual conditions, let $K>0$, and let $M$ be a martingale with continuous paths and $|M_t|\le K$ for all $t$. For $n\ge0$ define the dyadic sums

$$Q^n_t=\sum_{k\ge0}\bigl(M_{t\wedge(k+1)2^{-n}}-M_{t\wedge k2^{-n}}\bigr)^2 .$$

Then for every $T>0$, $(Q^n)_{n\ge0}$ is Cauchy in $L^2$ uniformly on $[0,T]$:

$$\mathbb E\sup_{t\le T}\bigl|Q^n_t-Q^m_t\bigr|^2\to0\qquad(n,m\to\infty),$$

and so converges in $L^2$ uniformly on $[0,T]$. Two estimates drive the proof: increments of $M$ over disjoint intervals are orthogonal, and $\mathbb E(Q^n_T)^2\le CK^4$ with an absolute constant $C$ (one may take $C=48$).

## Proof depends on

- [Optional stopping theorem in continuous time](../optional-stopping-theorem/stopped-value-ae-eq-cond-exp-of-le-of-co.md)
- [Local martingales and localization](local-martingales-and-localization.md)
- [Doob's $L^2$ maximal inequality in continuous time](../doob-s-maximal-inequalities/lintegral-i-sup-sq-le-of-continuous.md)
- [Orthogonality of martingale increments](../square-integrable-martingales/integral-sub-mul-eq-zero.md)

## Expansion

A full proof bounds $\mathbb E(Q^n_T)^2=\sum_k\mathbb E\Delta_k^4+2\sum_{j<k}\mathbb E\Delta_j^2\Delta_k^2$, where $\Delta_k$ are the dyadic increments, using $\mathbb E[\sum_{k>j}\Delta_k^2\mid\mathcal F_{(j+1)2^{-n}}]\le4K^2$ and $\mathbb E\sum_k\Delta_k^2\le4K^2$. Since $M_t^2-M_0^2-Q^n_t=2\sum_kM_{k2^{-n}}\bigl(M_{t\wedge(k+1)2^{-n}}-M_{t\wedge k2^{-n}}\bigr)$ is a martingale, so is $Q^n-Q^m$; the fourth-moment bound and uniform continuity of the paths on $[0,T]$ give $\mathbb E(Q^n_T-Q^m_T)^2\to0$, and Doob's $L^2$ maximal inequality makes the convergence uniform on $[0,T]$. It should check that for Brownian motion $B$ stopped at $\tau=\inf\{t:|B_t|\ge K\}$ the limit is $t\wedge\tau$.

## Sources

- D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Grundlehren 293, Springer, 1999, <https://link.springer.com/book/10.1007/978-3-662-06400-9>, quadratic variation of continuous martingales (topic).
- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in Mathematics 113, Springer, 1991, <https://link.springer.com/book/10.1007/978-1-4612-0949-2>, Ch. 1.5 (topic).
