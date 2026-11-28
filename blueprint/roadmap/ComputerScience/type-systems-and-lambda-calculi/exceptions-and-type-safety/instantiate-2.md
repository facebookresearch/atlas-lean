# Substitution lemma

Let `exn` be the exception type. If `b` has type `B` in the context
`Γ` extended by a new innermost variable of type `A`, and `s` has type `A` in `Γ`, then
`b.instantiate s` has type `B` in `Γ`.
