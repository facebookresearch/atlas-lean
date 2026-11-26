# Bang-bang optimal epidemic controls under an ICU constraint persist on infinite horizons

**Model.** For the SIR model with transmission control $b(t)\in[\beta_\star,\beta]\subset(0,1)$ and vaccination control $v(t)\in[0,v_M]$,

$$s'=-b\,s\,i-v\,s,\qquad i'=b\,s\,i-\gamma i,\qquad (s(0),i(0))=(s_0,i_0),$$

the triangle $\mathbb{T}=\{s,i\ge0,\ s+i\le1\}$ is forward invariant for all admissible controls. Consider the cost

$$J_T(b,v,s,i)=\int_0^T\bigl(\lambda_b(\beta-b(t))+\lambda_v v(t)+\lambda_i i(t)\bigr)\,dt,\qquad \lambda_b,\lambda_v,\lambda_i\ge0,$$

under the ICU state constraint $i(t)\le i_M$ for $t\in[0,T]$, with horizon $T\in(0,\infty]$, and initial data in the maximal viable set (the initial states from which the constraint can be maintained forever).

**Theorem (pattern preservation).**

1. *Optimal vaccination* ($b\equiv\beta$, control $v$). For every large enough finite $T$, every optimal control is bang-bang: $v_T=v_M$ on $(0,\tau^T_1)$ and $v_T=0$ afterwards, for some $\tau^T_1\in[0,T]$. The infinite-horizon problem has an optimal control of the same form with a finite switching time $\tau^\infty_1<\infty$.
2. *Optimal non-pharmaceutical intervention* ($v\equiv0$, $\lambda_i=0$, control $b$). For every large enough finite $T$, every optimal control has the form: $b=\beta$ (no intervention) on $(0,\tau^T_1)$, maximal intervention $b=\beta_\star$ on $(\tau^T_1,\tau^T_2)$, a boundary arc on $(\tau^T_2,\tau^T_3)$ along which $i\equiv i_M$, and $b=\beta$ after $\tau^T_3$. The infinite-horizon problem has an optimal control of the same structure with $\tau^\infty_3<\infty$.

On the boundary arc $i'=0$ forces $b(t)\,s(t)=\gamma$, and then $s'=-\gamma i_M$, so $b(t)=\gamma/\bigl(s(\tau_2)-\gamma i_M(t-\tau_2)\bigr)$.

**Abstract principle.** Both statements are instances of a general result: if a family of (possibly state-constrained) optimal control problems $\mathcal{F}_T$ is sequentially equi-coercive along $T_k\to\infty$ and $\Gamma$-converges to the infinite-horizon problem $\mathcal{F}_\infty$, then minimizers of $\mathcal{F}_{T_k}$ have subsequences converging to minimizers of $\mathcal{F}_\infty$, so any closed qualitative pattern shared by all finite-horizon optimal controls (bang-bang with at most $m$ switches, a fixed switching order) is inherited by an infinite-horizon optimal control. For epidemic models, equi-coercivity in the state comes from invariance of the compact triangle $\mathbb{T}$.

## Depends on

- [Maximal forward-invariant and viable sets of a delayed SIR model under an ICU constraint](maximal-viable-set-of-the-delayed-sir-model-with-an-icu-constraint.md)

## Expansion

1. Finite-horizon structure comes from Pontryagin's maximum principle with state constraints: the Hamiltonian is affine in $b$ and $v$, so controls are bang-bang except on constrained arcs.
2. $\Gamma$-convergence of $\mathcal{F}_T$ to $\mathcal{F}_\infty$ is proved in local Sobolev spaces $W^{1,p}_{\mathrm{loc}}$ for the states and weak-$*$ $L^\infty$ for the controls, using Carathéodory-Lipschitz bounds on the dynamics.
3. Bang-bang controls with at most $m$ switches form a weak-$*$ sequentially closed set, so the limit of finite-horizon optimal controls keeps the pattern; a uniform bound on the switching times gives finiteness of $\tau^\infty$.

## Sources

- M. Della Rossa, L. Freddi, *Pattern-preserving optimal control problems with increasing time horizon*, arXiv:2506.09970 (Theorem 2.7, Theorem 3.1, Corollary 3.2, Theorem 7.3; Section 8.2, Propositions 8.6 and 8.7). <https://doi.org/10.48550/arXiv.2506.09970> Published version: ESAIM: COCV, Volume 31, 2025, <https://doi.org/10.1051/cocv/2025088>.
