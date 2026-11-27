# Typing of values

`HasVTy sig Γ v A` is the judgment `Γ ⊢ v : A` of Pretnar 2015,
Fig. 6, for the global signature `sig`, which assigns to each operation `o` its parameter type
`(sig o).1` and result type `(sig o).2`. The context `Γ` lists the types of the free variables,
index `0` first, and `A_o`, `B_o` abbreviate `(sig o).1`, `(sig o).2`. A variable has the type
that `Γ` assigns to it; `()` has type `unit`; `true` and `false` have type `bool`. A function
`fun x ↦ c` has type `A → B ! Δ` when `c` has type `B ! Δ` under `x : A`. A handler has type
`A ! Δ ⇒ B ! Δ'` when its return clause has type `B ! Δ'` under `x : A`, every operation clause
`o(x; k) ↦ c` has type `B ! Δ'` under `x : A_o` and `k : B_o → B ! Δ'`, and every operation of
`Δ` that it does not handle lies in `Δ'`.
