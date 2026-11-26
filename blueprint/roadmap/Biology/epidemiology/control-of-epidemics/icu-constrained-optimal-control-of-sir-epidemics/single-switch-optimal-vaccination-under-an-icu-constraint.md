# Single-switch optimal vaccination under an ICU constraint

**Setting.** Consider the controlled SIR model $s'=-\beta si-v(t)s$, $i'=\beta si-\gamma i$, $(s(0),i(0))=(s_0,i_0)$, with vaccination rate $v(t)\in[0,v_M]$, ICU capacity $i_M\in(0,1]$, and cost

$$J(v)=\int_0^T\big(\lambda_v v(t)+\lambda_i i(t)\big)\,dt,\qquad \lambda_v,\lambda_i\ge0,\ (\lambda_v,\lambda_i)\ne(0,0),$$

to be minimized subject to $i(t)\le i_M$ on $[0,T]$. Let $A$ be the no-effort set and $B$ the viable set of [Viable and no-effort sets of the SIR model under an ICU constraint](viable-and-no-effort-sets-of-the-sir-model-under-an-icu-constraint.md), and let $\bar t(s_0,i_0)$ be the latest time, over all controls, at which $s$ reaches the herd immunity level $\gamma/\beta$; assume $T>\bar t(s_0,i_0)$.

**Theorem.** For $(s_0,i_0)\in B$:

1. An optimal control exists (more generally for any normal convex integrand cost).
2. Every optimal control is bang-bang with at most one switch: there is $t_\star\in[0,T]$ with

$$\hat v(t)=\begin{cases}v_M,& t\in(0,t_\star),\\ 0,& t\in(t_\star,T),\end{cases}$$

and $t_\star=T$ if and only if $\lambda_v=0$. At the switch the state lies in the no-effort set, $\hat x(t_\star)\in A$.

3. If $\lambda_i=0$ (pure vaccination cost) the optimal control is unique and has the feedback form $\hat v=v_M$ on $B\setminus A$ and $\hat v=0$ on $A$: vaccinate at full rate exactly until the uncontrolled epidemic would respect the ICU capacity. For small $\lambda_i$ (or large $\lambda_v$) the optimal control coincides with this one.

4. The infinite-horizon problem is the $\Gamma$-limit of the finite-horizon problems as $T\to\infty$; limits of finite-horizon optimal controls are optimal, and for $\lambda_i=0$ the infinite-horizon optimal control is unique, of the same single-switch form with $t_\star\le\bar t(s_0,i_0)$.

## Expansion

The proof uses a state-constrained Pontryagin maximum principle. The Hamiltonian is affine in $v$ (the control enters through $-v s$ in the $s$-equation and $\lambda_v v$ in the cost), so optimal controls are bang-bang away from singular arcs; the sign analysis of the costates and of the state-constraint multiplier excludes singular arcs and shows the switching function changes sign at most once, from full vaccination to none. Stopping before reaching $A$ is infeasible, since the uncontrolled trajectory would later exceed $i_M$; continuing inside $A$ only adds cost when $\lambda_i=0$, which yields the feedback law. Uniqueness in general reduces to uniqueness for the unconstrained problem started at the time the maximal-vaccination trajectory enters $A$.

## Depends on

- [Viable and no-effort sets of the SIR model under an ICU constraint](viable-and-no-effort-sets-of-the-sir-model-under-an-icu-constraint.md)

## Sources

- Matteo Della Rossa, Lorenzo Freddi, Dan Goreac, "Optimality of vaccination for an SIR epidemic with an ICU constraint", arXiv:2407.08425 (2024): Section 3.2 (general existence theorem and its corollary), Section 4 (assumption on the horizon, structure theorem for optimal controls, propositions on the switching time and on small $\lambda_i$, uniqueness discussion), Section 5 (reduction to a finite horizon, $\Gamma$-convergence theorem and corollaries). <https://doi.org/10.48550/arXiv.2407.08425> Published version: J Optim Theory Appl 204, 8 (2025), <https://doi.org/10.1007/s10957-024-02598-w>.
