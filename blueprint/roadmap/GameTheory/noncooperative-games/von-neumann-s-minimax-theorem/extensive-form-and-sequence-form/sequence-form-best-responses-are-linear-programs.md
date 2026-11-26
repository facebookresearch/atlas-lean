# Sequence-form best responses are linear programs

For a fixed realization plan $y$ of player $2$, a realization plan $x$ of player $1$ is a best response if and only if it is optimal for the linear program $\max\, x^\top (A_1 y)$ subject to $Ex = e$, $x \ge 0$, whose dual is $\min\, e^\top p$ subject to $E^\top p \ge A_1 y$. Both programs are feasible and bounded and have equal optimal values.

## Proof sketch

The feasible set is the polytope of realization plans, nonempty and bounded; dual feasibility is witnessed by backward accumulation of the maximal payoffs at each information set. Strong LP duality gives equality of optima.

## Depends on

- [Sequence-form payoff matrices](sequence-form-payoff-matrices.md)

## Proof depends on

- [The realization plan polytope is the convex hull of pure realization plans](the-realization-plan-polytope-is-the-convex-hull-of-pure-realization-plans.md)

## Sources

- Bernhard von Stengel, "Equilibrium Computation for Two-Player Games in Strategic and Extensive Form", Algorithmic Game Theory, Cambridge University Press, 2007.
