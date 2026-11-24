# Global convergence for reversible Michaelis–Menten kinetics, via LaSalle

For positive
rate constants, every solution with nonnegative initial data and positive totals
`E_T = e₀ + c₀`, `S_T = s₀ + c₀ + p₀` converges to the unique equilibrium `x*` of its
compatibility class (`existsUnique_equilibrium`), which is positive.

Proof: `lasalle_of_antitoneOn` on the compact, convex, forward-invariant class
`K = {x ≥ 0 | x₂ + x₁ = E_T, x₀ + x₁ + x₃ = S_T}` with the Lyapunov function
`G = pseudoHelmholtz x*` (`IsSolution.antitoneOn_pseudoHelmholtz`). A solution in `K` along
which `G` is constant is positive at `t = 2` (`IsSolution.pos`), so there its orbital derivative
vanishes, hence it sits at an equilibrium of the class, i.e. at `x*`; since `G` is constant, the
Gibbs inequality `eq_of_pseudoHelmholtz_eq` forces the starting point to be `x*` as well. So
the largest forward-invariant set on which `G` is constant is `{x*}`.
