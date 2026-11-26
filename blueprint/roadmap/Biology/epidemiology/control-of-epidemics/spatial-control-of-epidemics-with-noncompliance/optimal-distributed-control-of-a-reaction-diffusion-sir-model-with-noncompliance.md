# Optimal distributed control of a reaction-diffusion SIR model with contagious noncompliance

On a bounded Lipschitz domain $\Omega\subset\mathbb{R}^n$ with no-flux boundary conditions, let $S,I,R$ be the compliant and $S^*,I^*,R^*$ the noncompliant susceptible, infectious and recovered densities, $N^*=S^*+I^*+R^*$, and $I_M=(1-\alpha)I+I^*$ the actively mixing infectious density. With a diffusion rate $d_Z>0$ for each class $Z$, birth rate $b(x)\ge0$ (a fraction $\xi\in[0,1]$ born compliant), death rate $\delta>0$, transmission $\beta>0$, recovery $\gamma>0$ and maximal noncompliance transmission $\bar\mu>0$, the controlled system is

$$\partial_t S - d_S\Delta S = \xi b - \beta(1-\alpha)S I_M - (\bar\mu-\mu)S N^* + \nu S^* - \delta S,$$

$$\partial_t I - d_I\Delta I = \beta(1-\alpha)S I_M - \gamma I - (\bar\mu-\mu)I N^* + \nu I^* - \delta I,$$

$$\partial_t R - d_R\Delta R = \gamma I - (\bar\mu-\mu)R N^* + \nu R^* - \delta R,$$

and symmetrically for the noncompliant classes ($S^*$ gains $(1-\xi)b$ and $(\bar\mu-\mu)SN^*$, loses $\beta S^* I_M$, $\nu S^*$ and $\delta S^*$; similarly for $I^*,R^*$). The distributed controls are $u=(\alpha,\mu,\nu)$ with $\alpha\in[\underline\alpha,1]$ (reduced infectivity of compliant people under non-pharmaceutical interventions), $\mu\in[0,\bar\mu]$ (reduced spread of noncompliance) and $\nu\in[0,\bar\nu]$ (rate at which noncompliant people return to compliance).

**Theorem.**

1. (Global well-posedness.) For nonnegative bounded data and admissible controls, the unique local classical solution stays bounded in every $L^p(Q_t)$, $p<\infty$, and then in $L^\infty(Q_t)$ on every finite time interval; hence it exists globally in time.
2. (Control-to-state map.) The control-to-state map $\mathcal{M}:u\mapsto y=(S,I,R,S^*,I^*,R^*)$ on $L^p$ admissible controls is Lipschitz for $p\ge2$, weak-to-strong continuous into $L^{\max_i p^i_s}(Q_T)^6$ for $p\ge\max\{2,\max_i p^i_s\}$, and Fréchet differentiable into $[L^{p/2}(Q_T)]^6$, the derivative in direction $h$ solving the linearized system $y_t-D\Delta y=F_u h+F_y y$ with zero initial data.
3. (Existence and optimality.) For cost functionals $\mathcal{J}(y,u)$ built from $L^{p^i_s}$ norms of polynomial state quantities (for example total infections $I+I^*$ and total noncompliance $N^*$) and polynomial control costs, the problem $\min_u\mathcal{J}(\mathcal{M}(u),u)$ admits an optimal control $u^\circ$, and $u^\circ$ satisfies a first-order optimality system: state equation, backward adjoint equation, and the variational inequality $\langle\mathcal{L}_u(y^\circ,u^\circ,\Phi^\circ),u-u^\circ\rangle\ge0$ for all admissible $u$.

## Expansion

1. Summing all six equations gives a linear heat equation for the total population, which is bounded; Pierre's $L^p$-duality estimates for systems with mass control upgrade this to $L^p$ bounds, and the quadratic reaction terms then allow a bootstrap to $L^\infty$.
2. Weak-to-strong continuity of $\mathcal{M}$ comes from compactness of the parabolic solution operator (Aubin-Lions) together with the uniform bounds; existence of an optimal control follows by the direct method with weak lower semicontinuity of $\mathcal{J}$.
3. Differentiability of $\mathcal{M}$ and the Lagrangian formalism give the adjoint system and the pointwise projection characterization of $u^\circ$.

## Sources

- M. Bongarti, C. Parkinson, W. Wang, *Optimal control of a reaction-diffusion epidemic model with noncompliance*, arXiv:2407.17298 (Theorems 2.1 and 2.2; Theorem 3.2, Propositions 3.3–3.5, Corollary 3.1, Theorems 3.10–3.12). <https://doi.org/10.48550/arXiv.2407.17298> Published version: European Journal of Applied Mathematics 37 (2025) 313–338, <https://doi.org/10.1017/s0956792525000130>.
