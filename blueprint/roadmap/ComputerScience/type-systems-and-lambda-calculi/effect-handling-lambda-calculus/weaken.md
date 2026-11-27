# Weakening for values

If `Γ ⊢ v : A`, then for every block `Θ` of new innermost
variables, `v` with every free variable shifted up by the length of `Θ` has type `A` in
`Θ ++ Γ`.
