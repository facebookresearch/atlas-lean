# Kolmogorov–Petrovsky–Piskunov existence from the unstable branch

For `c ≥ 2 √(r D)`,
any solution of the profile equation on `z < 0` with the properties of the unstable branch
(quadrant orientation, `(U, U') → (1, 0)` at `-∞`; exactly the first four conclusions of
`PlanarShooting.exists_unstableBranch`) yields a strictly decreasing front of speed `c`.

Proof: the branch enters the trapping triangle at some `z₀ < 0`. The maximal solution through
that point (`ode_maximal_solution_exit_compact`) stays in the triangle, hence in a compact box,
so it cannot end at a finite time and lives on `[z₀, ∞)`. Gluing it to the branch at `z₀` gives
a global solution, which `isFront_of_unstableBranch` turns into a front. No uniqueness theorem
is needed: the two pieces meet at one point with equal data.
