# Phase-corrected linear noise approximation

**Setting.** A reaction network with $n$ species and $r$ reactions has copy-number process $Y(t)\in\mathbb Z_{\ge0}^n$ that jumps by the stoichiometric vector $\nu_j$ at rate $\pi_j(Y)$, $j=1,\dots,r$; equivalently $Y(t)=Y(0)+\sum_j\nu_jN_j\bigl(\int_0^t\pi_j(Y(s))\,ds\bigr)$ with independent unit-rate Poisson processes $N_j$. Assume density dependence with system size $\Omega$: $\pi_j(y)=\Omega\rho_j(y/\Omega)$ with smooth macroscopic rates $\rho_j$, and set $X(t)=Y(t)/\Omega$. The reaction rate equation (RRE) is

$$\dot x=F(x)=\sum_{j=1}^r\nu_j\rho_j(x),$$

with Jacobian $J(x)=\partial F/\partial x$, stoichiometry matrix $S=[\nu_1\cdots\nu_r]$ and $E(x)=S\,\mathrm{diag}\bigl(\sqrt{\rho_1(x)},\dots,\sqrt{\rho_r(x)}\bigr)$.

**Phase.** Fix a set of reference RRE trajectories $\Gamma=\bigcup_{\ell=1}^{L}\{x^{(\ell)}(t):t\ge0\}$ (for an attracting limit cycle, one trajectory on the cycle; for several stable equilibria, one trajectory converging to each) and a metric $d$ on state space. The *phase* of a state $X$ is the time coordinate $s$ of its closest reference point,

$$(j,s)=\arg\min_{\ell,\ t\ge0}d\bigl(X,x^{(\ell)}(t)\bigr),\qquad G(X)=x^{(j)}(s).$$

**Statement (pcLNA scheme).** The phase-corrected LNA uses the ansatz $X(t)=G(X(t))+\Omega^{-1/2}\kappa(t)$. With the LNA fundamental matrices $C^{(\ell)}$ and covariances $D^{(\ell)}$ precomputed once along each reference trajectory, start from $G(X(0))=x^{(j_0)}(s_0)$, $\kappa(s_0)=\Omega^{1/2}(X(0)-x^{(j_0)}(s_0))$, and for $i=1,2,\dots$:

1. draw $\xi\sim\mathrm{MVN}\bigl(C^{(j_{i-1})}(s_{i-1},s_{i-1}+\Delta t)\,\kappa(s_{i-1}),\ D^{(j_{i-1})}(s_{i-1},s_{i-1}+\Delta t)\bigr)$;
2. set $X(t_i)=x^{(j_{i-1})}(s_{i-1}+\Delta t)+\Omega^{-1/2}\xi$;
3. phase-correct: $G(X(t_i))=x^{(j_i)}(s_i)$ and $\kappa(s_i)=\Omega^{1/2}\bigl(X(t_i)-x^{(j_i)}(s_i)\bigr)$.

For RREs $\dot x=F(x,\alpha)$ near a non-hyperbolic equilibrium $x_{\alpha_p}$ (Hopf bifurcation, or a fold giving bistability), the phase metric is taken in approximate centre coordinates: with $R_c$ an $n\times n_0$ matrix whose columns span the centre eigenspace of $J(x_{\alpha_p},\alpha_p)$ and $P_c=(R_c^\top R_c)^{-1}R_c^\top$,

$$d(y,x)=\bigl\|P_c(y-x)\bigr\| .$$

This choice is justified by the centre manifold theorem and a Takens normal form: under a $k$-Sternberg nonresonance condition there are local $C^k$ coordinates $(u,v,w)$ in which $\dot u=f(u,\alpha)$, $\dot v=A_s(u,\alpha)v$, $\dot w=A_u(u,\alpha)w$, so the persistent non-linear behaviour lives in the centre coordinates $u$ while the stable coordinates relax linearly.

## Depends on

- [Linear noise approximation of density-dependent reaction networks](linear-noise-approximation-of-density-dependent-reaction-networks.md)

## Expansion

The plain LNA fails for non-linear dynamics because of *phase drift*: after some time the stochastic state is at a different stage of the deterministic dynamics than $x(t)$, yet the LNA drift and diffusion are still evaluated along $x(t)$. Re-anchoring at the phase of the current state keeps the deterministic reference and the stochastic state aligned, so each step is a short LNA transition from the right place and the residual fluctuation $\kappa$ stays small. Because the reference ODEs and the matrices $C$, $D$ are solved only once, simulation costs little more than the plain LNA. Projecting onto the centre eigenspace measures progress along the slow, non-linear directions (the angle around a limit cycle, or position along the single centre direction separating two basins), so the phase map tracks oscillation phase and sends a state to the reference trajectory of the attractor it is approaching, which captures noise-induced switching between stable states.

## Sources

- Frederick Truman-Williams, Giorgos Minas, "Simulating stochastic population dynamics: The Linear Noise Approximation can capture non-linear phenomena", *SIAM Journal on Applied Dynamical Systems* 25(3) (2026), 1911–1938, Section "The phase-corrected Linear Noise Approximation (pcLNA)", Section "Hopf bifurcation systems", Section "Bi-stable systems", Theorem 1 and Theorem 2, <https://doi.org/10.1137/25m1789792> (preprint arXiv:2504.15166).
