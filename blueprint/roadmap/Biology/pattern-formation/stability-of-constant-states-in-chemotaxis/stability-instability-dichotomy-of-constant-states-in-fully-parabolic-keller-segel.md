# Stability–instability dichotomy of constant states in the fully parabolic Keller–Segel system

Consider the fully parabolic Keller–Segel system on $\mathbb R^d$, $d\ge2$, with signal relaxation and decay normalized to one,
$$\partial_t b-\Delta b=-\nabla\cdot(b\nabla a),\qquad \partial_t a-\Delta a=b-a,$$
where $b$ is cell density and $a$ chemoattractant concentration. Every constant pair $(A,A)$, $A\ge0$, is an equilibrium. Write $n=b-A$, $c=a-A$ and take $(n_0,c_0)\in H^s\times H^{s+1}$ with integer $s>d/2$. The critical density is $A_{\rm crit}=1$.

**Theorem.**

1. *Subcritical, $0\le A<1$.* If $\|\widehat{n_0}\|_{L^1}+\||\xi|^j\widehat{c_0}\|_{L^1}\le\delta_j$ ($j\in\{0,1\}$) is small, there is a unique global smooth solution, it stays small in the same norm, and $\|D^m n(t)\|_{L^2}+\|D^m c(t)\|_{L^2}\le Ct^{-m/2}$, $\|D^m(n-c)(t)\|_{L^2}\le C\big(t^{-(m/2+d/4+1)}+At^{-(m/2+1)}\big)$ for $t>1$.
2. *Critical, $A=1$.* If moreover $n_0,\nabla c_0\in L^1$, $\widehat{c_0}\in L^\infty$ and $\|\widehat{n_0}\|_{L^1\cap L^\infty}+\||\xi|\widehat{c_0}\|_{L^1\cap L^\infty}\le\delta$ is small, the solution is global, stays small, and decays at half the heat rate: $\|D^m n(t)\|_{L^2}+\|D^m c(t)\|_{L^2}\le Ct^{-\frac12(\frac m2+\frac d4)}$.
3. *Supercritical, $A>1$.* The equilibrium is nonlinearly unstable: there are $C_0>1$, $\eta_0>0$ such that for every $\eta\in(0,\eta_0)$ some data of $H^s\times H^{s+1}$ size $\eta$ produce, at time $T_\eta=\frac{4A}{(A-1)^2}\ln\frac{C_0\eta_0}{\eta}$, a solution with $\min\{\|n\|_{L^2},\|c\|_{L^2},\|\nabla c\|_{L^2}\}\ge\eta_0/4$.

A consequence for $A=0$, $d=2$: there are global bounded solutions of every mass, so unlike the case without signal decay there is no critical-mass blow-up threshold when the signal degrades.

## Expansion

In Fourier variables the linearization about $(A,A)$ is the $2\times2$ system $\hat n_t=-|\xi|^2\hat n+A|\xi|^2\hat c$, $\hat c_t=\hat n-(1+|\xi|^2)\hat c$. Its determinant $|\xi|^2(1+|\xi|^2-A)$ is positive for all $\xi\ne0$ iff $A\le1$; for $A>1$ the band of low frequencies $|\xi|^2<A-1$ has a positive eigenvalue, and the escape time $T_\eta$ is calibrated to the growth rate $(A-1)^2/(4A)$. This is the whole-space version of the Keller–Segel aggregation instability. For $A<1$ the slow eigenvalue behaves like $-(1-A)|\xi|^2$ near $\xi=0$, giving heat-type decay; at $A=1$ it degenerates to order $|\xi|^4$, which halves the decay exponents. Nonlinear stability follows by controlling $\nabla\cdot(n\nabla c)$ in Wiener-algebra norms $\|\hat f\|_{L^1}$; instability by seeding the fastest-growing mode and showing it dominates the nonlinear remainder up to the escape time.

## Sources

- J. Ahn, J.-M. Kim, J. Kim, *Stability and instability for the fully parabolic Keller-Segel system around constant equilibrium* (2026), Theorems 1.1, 1.2 and 1.3, with Remarks 1.2 and 1.3. <https://doi.org/10.48550/arXiv.2607.10384>
