# Bang–bang structure of optimal ICU-constrained epidemic control

**Problem.** For the controlled SIR system $\dot s=-(\beta-u)si$, $\dot i=(\beta-u)si-\gamma i$ with control $u(t)\in[0,u_{\max}]$, $u_{\max}<\beta$, and initial state in the viable set $\mathcal B$ (states from which some control keeps $i\le i_M$ forever), minimize

$$J^\infty(u)=\int_0^\infty\big[\lambda_1u(t)+\lambda_2 i(t)\big]\,dt,\qquad \lambda_1>0,\ \lambda_2\ge0,$$

subject to the ICU constraint $i(t)\le i_M$ for all $t\ge0$. The finite-horizon problem $\mathcal P^T$ integrates over $[0,T]$ only. The *safe set* $\mathcal A\subset\mathcal B$ consists of states from which $u\equiv0$ already respects the constraint.

**Theorem (existence and convergence).** For a running cost $f_0(t,s,i,u)\ge0$ that is a normal integrand, lower semicontinuous in $(s,i,u)$ and convex in $u$, the infinite-horizon problem has an optimal solution; for the linear cost above every initial state of $\mathcal B$ with $i_0>0$ admits an optimal control with finite cost, and its final susceptible fraction satisfies $s_\infty<\gamma/\beta$. The finite-horizon problems $\Gamma$-converge to the infinite-horizon one as $T\to\infty$, and weak-$*$ limits of finite-horizon optimal controls are optimal for the infinite horizon.

**Theorem (structure, safe start).** If $(s_0,i_0)\in\mathcal A\setminus\partial\mathcal A$, there is an optimal control of the form

$$u^\infty(t)=\begin{cases}0,& 0<t<\sigma_1,\\ u_{\max},& \sigma_1<t<\sigma_2,\\ 0,& t>\sigma_2,\end{cases}$$

for some $0\le\sigma_1\le\sigma_2<\infty$ (bang–bang with at most two switches).

**Theorem (structure, constrained start).** If $(s_0,i_0)\in\mathcal B\setminus\mathcal A$ and the ICU boundary is reached, there is an optimal control with times $0\le\tau_0\le\tau_1\le\tau_2\le\tau_3<\infty$ such that $u=0$ on $(0,\tau_0)$, $u=u_{\max}$ on $(\tau_0,\tau_1)$, then on the boundary arc $(\tau_1,\tau_2)$ where $i\equiv i_M$,

$$u(t)=\beta-\frac{\gamma}{s(\tau_2)+\gamma i_M(\tau_2-t)},$$

then $u=u_{\max}$ on $(\tau_2,\tau_3)$ and $u=0$ after $\tau_3$.

## Expansion

Pontryagin's maximum principle with a state constraint gives a switching function $\psi$ compared with $\lambda_1$: the Hamiltonian is linear in $u$, so $u=u_{\max}$ where $\psi>\lambda_1$ and $u=0$ where $\psi<\lambda_1$; singular arcs with $\psi\equiv\lambda_1$ can occur only while $i=i_M$. Keeping $i$ constant at $i_c$ forces $(\beta-u)s=\gamma$, and since then $\dot s=-\gamma i_c$, $s$ decreases linearly, which yields the explicit feedback on the boundary arc. Nonnegativity and monotonicity of the costates rule out further switches, giving the $0$–$u_{\max}$–$0$ pattern away from the constraint.

## Depends on

- [Viable and safe sets of the SIR model under an ICU constraint](viable-and-safe-sets-of-the-sir-model-under-an-icu-constraint.md)

## Sources

- Lorenzo Freddi, Dan Goreac, "Infinite horizon optimal control of a SIR epidemic under an ICU constraint", arXiv:2306.10513: Theorem 5.1 (existence for convex normal integrands), Proposition 6.2 and Corollary 6.3 (linear cost), Theorems 7.2 and 7.5 ($\Gamma$-convergence of finite horizons), Theorem 8.5 and Proposition 8.6 (singular and boundary arcs), Theorems 9.1, 9.6, 9.7, 9.9 (structure of optimal controls). <https://doi.org/10.48550/arXiv.2306.10513> Published version: Journal of Convex Analysis, 31(4), 2024.
