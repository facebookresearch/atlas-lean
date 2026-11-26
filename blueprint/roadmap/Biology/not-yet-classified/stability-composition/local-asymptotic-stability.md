# Deficiency-zero theorem, local asymptotic stability

Let `N` be a weakly reversible
mass-action network of deficiency zero with positive rate constants `k`, and let `x₀` be a
positive state. The stoichiometric compatibility class of `x₀` contains exactly one positive
equilibrium, and every positive equilibrium `xstar` in that class is locally asymptotically
stable relative to the class: every state of the class close enough to `xstar` starts a global
forward solution; for every `ε > 0`, every solution that starts in the class close enough to
`xstar` stays within `ε` of it for all `t ≥ 0`; and every solution that starts in the class
close enough to `xstar` converges to it. Distances are sup-norm distances on `S → ℝ`, and
solutions have two-sided derivatives at every `t ≥ 0`.

Existence and stability hold across classes as well
(`ComplexBalancedStability.exists_solution_of_near_all_classes` and
`ComplexBalancedStability.stable_all_classes`). Convergence is local and relative to the class;
global convergence from arbitrary positive states is not claimed.

## Sources

- Feinberg (1987), Theorem 6.1.1(iii) and Section 5.2.
