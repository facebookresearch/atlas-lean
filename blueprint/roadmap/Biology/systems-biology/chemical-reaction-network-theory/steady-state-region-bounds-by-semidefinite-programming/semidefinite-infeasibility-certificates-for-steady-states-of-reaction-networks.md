# Semidefinite infeasibility certificates for steady states of uncertain reaction networks

**Problem.** A biochemical reaction network with mass-action kinetics is

$$\dot x = S\,v(x, p), \qquad v_j(x, p) = p_j\prod_{k=1}^n x_k^{\sigma_{jk}}, \quad j = 1, \dots, m,$$

with concentrations $x \in \mathbb{R}^n$, stoichiometric matrix $S \in \mathbb{R}^{n\times m}$, rate constants $p$ and integer reactant coefficients $\sigma_{jk}$. Given a box $\mathcal{P}$ of admissible parameters, the goal is an outer bound on the set of all steady states $\{x : Sv(x,p) = 0 \text{ for some } p \in \mathcal{P}\}$ (global sensitivity analysis of steady states). For a candidate box $\mathcal{X}$ in state space, the feasibility problem (P) asks for $x \in \mathcal{X}$, $p \in \mathcal{P}$ with $Sv(x,p) = 0$.

**Relaxation.** Collect a vector $\xi$ of monomials, with first entry $1$, such that each steady-state equation and each box constraint is a quadratic form in $\xi$: $Sv(x,p) = 0$ becomes $\xi^\top Q_i\xi = 0$ ($i = 1, \dots, n$) and the bounds become quadratic inequalities. Setting $X = \xi\xi^\top$ and dropping $\mathrm{rank}\,X = 1$ gives the semidefinite feasibility problem (RP): find symmetric $X \succeq 0$ with $X_{11} = 1$, $\mathrm{tr}(Q_iX) = 0$ and the linearized box constraints. If (P) is feasible, so is (RP).

**Theorem.** If the Lagrange dual of (RP), whose free variables are the multipliers $\lambda_1 \ge 0$, $\lambda_2 \ge 0$ (box constraints), $\lambda_3 \succeq 0$ (semidefiniteness) and $\nu_1, \dots, \nu_{n+1}$ (equalities, with $\nu_{n+1}$ attached to $X_{11} = 1$), has a feasible solution with $\nu_{n+1} > 0$, then (RP) and hence (P) are infeasible: the box $\mathcal{X}$ contains no steady state for any parameter in $\mathcal{P}$.

## Proof sketch

The dual constraints are homogeneous, so the dual optimal value is either $0$ or $+\infty$, and a feasible point with $\nu_{n+1} > 0$ can be scaled to make the dual objective arbitrarily large. Weak duality for semidefinite programs gives $d^* \le p^*$, where $p^* = 0$ if the relaxation is feasible and $+\infty$ otherwise, so $d^* = \infty$ forces infeasibility. A dual feasible point is thus a numerical certificate, checkable independently of the solver, that a region of state space is free of steady states. Bisecting the state-space box and discarding certified-infeasible pieces yields guaranteed outer approximations of the steady-state region; applied to a conversion reaction and an enzymatic cycle, this bounds how far steady states can move under given parameter uncertainty.

## Sources

- Steffen Waldherr, Rolf Findeisen and Frank Allgöwer, "Global Sensitivity Analysis of Biochemical Reaction Networks via Semidefinite Programming", *IFAC Proceedings Volumes* 41 (2008), 9701–9706, <https://doi.org/10.3182/20080706-5-kr-1001.01641>. Preprint version: arXiv:0904.4592 (2009), problem statement (Section 2), semidefinite relaxation (Section 3.1), Theorem 1 (Section 3.2), and the bounding algorithm (Section 4), <https://doi.org/10.48550/arXiv.0904.4592>.
