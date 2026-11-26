# Renaming a context

Renames the computation of a `do` frame by the renaming lifted past
its bound variable (`References.Term.liftRen`), the handler literal of a handler frame as
`Val.ren ρ` renames it (the return clause by the lifted renaming, the operation clauses by
`Clauses.ren ρ`), and the inner context by `ρ`.
