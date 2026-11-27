# Tumour elimination and optimal boundary drug injection in a reaction–diffusion chemotherapy model

**Model.** Let $\Omega\subset\mathbb R^n$ be a bounded smooth domain with boundary $S$, and let $N,T,I\ge 0$ be the densities of normal, tumour and immune cells and $U\ge 0$ the drug concentration. They solve the quasilinear system

$$\partial_t Z=\nabla\cdot\big(d_Z(x,t,Z)\nabla Z\big)+F_Z(N,T,I,U),\qquad Z\in\{N,T,I,U\},$$

with

$$\begin{aligned} F_N&=r_1N(1-b_1N)-c_4TN-a_3(1-e^{-U})N,\\ F_T&=r_2T(1-b_2T)-c_2IT-c_3TN-a_2(1-e^{-U})T,\\ F_I&=r_3I(1-b_3I)+s(x,t)+\frac{\rho IT}{\alpha+T}-c_1IT-k_1I-a_1(1-e^{-U})I,\\ F_U&=-k_2(x,t,N,T,I,U)\,U . \end{aligned}$$

The cells satisfy no-flux boundary conditions, and the drug is injected through the boundary at rate $v(x,t)\ge0$, switched off when normal cells fall below a level $a_0\in(0,1/b_1)$:

$$d_4\,\partial_\nu U=v(x,t)\,H(N-a_0)\quad\text{on }S\times(0,\infty),$$

where $H$ is a $C^1$ Heaviside-type function ($H(s)=0$ for $s<0$, $H(s)=1$ for $s\ge\delta$). Diffusivities are bounded below by $\delta_0>0$ and growth coefficients satisfy $0<r_0\le r_i\le R_0$. The parameters $a_i$, $c_i$, $k_1$, $\alpha$, $\rho$ are positive, $k_2$ is bounded with $k_2\ge k_0>0$ for a constant $k_0$, and the inputs $v\ge0$ on $S$ and $s\ge0$ in $\Omega$ satisfy $\|v\|_{L^\infty(S\times(0,\tilde t))}+\|s\|_{L^\infty(\Omega\times(0,\tilde t))}\le A_1$ for every $\tilde t>0$ with one constant $A_1$, so the bound is uniform in time (the source's (H1), (H2) and (H4)).

**Theorem (well-posedness and attractor).** For nonnegative bounded initial data there is a global nonnegative bounded weak solution; it is classical under smoothness and compatibility conditions and unique when the diffusivities are Hölder continuous in $(x,t)$. If the coefficients are time independent, the solution is bounded uniformly in time and the solution semigroup has a maximal attractor in $L^\infty_+(\Omega)$.

**Theorem (tumour elimination).** Suppose in addition $\|v(t)\|_{L^\infty(S)}\to0$, the immune source satisfies $\inf s\ge\beta>0$, $\inf_\Omega I_0>0$, and, for treatment periods of length $L$, the tumour reproduction coefficient satisfies $|r_2|\le R_0$ on a terminal window $(jL-\xi,jL)$ of each period, $j\ge K_0$. Then $\|U(t)\|_{L^p(\Omega)}\to0$ for every $p<\infty$, and there are $R_*>0$ and $\tau_*$ such that $R_0<R_*$ implies

$$\|T(t)\|_{L^\infty(\Omega)}\le Ce^{-\kappa t},\qquad t\ge\tau_*,$$

for constants $C,\kappa>0$: the tumour is eliminated exponentially fast.

**Theorem (optimal injection rate).** Assume moreover that the diffusivities $d_i(x,t,z)$ are Hölder continuous in $(x,t)$. Fix $t_0>0$, a constant $A_0>A_1$, $\lambda>0$, the admissible rates $U_{ad}=\{v\in L^\infty(S\times(0,t_0)):0\le v\le A_0\}$ and the cost

$$J(v)=\int_\Omega T(x,t_0)\,dx+\lambda\|v\|_{L^\infty(S\times(0,t_0))}.$$

For the minimization of $J$ over $U_{ad}$, subject to the state constraints $\int_\Omega N(x,t)\,dx\ge a_0$ and $\int_\Omega I(x,t)\,dx\ge b_0$ on $[0,t_0]$ with $0<a_0<\int_\Omega N_0$ and $0<b_0<\int_\Omega I_0$ (assumed feasible), an optimal injection rate $u\in U_{ad}$ exists, and it satisfies a first-order optimality condition expressed through the weak solution of the linearized (sensitivity) system whose drug boundary condition is $d_4\partial_\nu U^*=vH(N-a_0)+uH'(N-a_0)N^*$.

## Expansion

Boundedness comes from an $L^1$ bound plus an Alikakos–Moser type iteration (an $L^\infty$ estimate for subsolutions with nonlinear boundary flux whose constant does not depend on the time horizon). The decay of the drug follows from the vanishing boundary input. On each window where tumour reproduction is small, the immune kill term $c_2IT$ dominates, so $T$ contracts by a fixed factor per period while it can grow at most linearly in between, giving exponential decay. Existence of an optimal control uses compactness of the control-to-state map, which is continuous into $L^\infty$, together with a penalty for the integral constraints.

## Sources

- Jeff Morgan, Bao Quoc Tang, Hong-Ming Yin, "Existence, stability and optimal drug dosage for a reaction-diffusion system arising in a cancer treatment", Communications in Mathematical Sciences 24 (2026), 1543–1561, <https://doi.org/10.4310/cms.260601202610>. Published version of arXiv:2408.02227, cited next; locators there refer to the arXiv version.
- Jeff Morgan, Bao Quoc Tang, Hong-Ming Yin, "Existence, Stability and Optimal Drug Dosage for a Reaction-Diffusion System Arising in a Cancer Treatment", arXiv:2408.02227 (2024): system (2.x) with hypotheses (H1)–(H6), Theorem 2.3, Proposition 2.4, Corollary 2.5, Lemma 2.6, Theorem 2.7, Theorems 3.1 and 3.3. <https://doi.org/10.48550/arXiv.2408.02227>
