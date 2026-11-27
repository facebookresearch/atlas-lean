# Weakening for computations

If `Γ ⊢ c : C`, then for every block `Θ` of new innermost
variables, `c` with every free variable shifted up by the length of `Θ` has type `C` in
`Θ ++ Γ`.
