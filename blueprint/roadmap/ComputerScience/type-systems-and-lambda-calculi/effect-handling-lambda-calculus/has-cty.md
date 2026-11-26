# Typing of computations

`HasCTy sig Γ c C` is the judgment `Γ ⊢ c : C` of Pretnar 2015,
Fig. 6, for the global signature `sig`, with the generic effect `op o v` in place of
`op(v; y. c)`; `A_o` and `B_o` abbreviate `(sig o).1` and `(sig o).2`. It is the least relation
closed under the following rules. If `v : A`, then `return v` has type `A ! Δ` for every `Δ`. If
`o ∈ Δ` and `v : A_o`, then `op o v` has type `B_o ! Δ`. If `c₁ : A ! Δ` and `c₂ : B ! Δ` under
`x : A`, then `do x ← c₁ in c₂` has type `B ! Δ`. If `v : bool`, `c₁ : C` and `c₂ : C`, then
`if v then c₁ else c₂` has type `C`. If `v : A → B ! Δ` and `w : A`, then `v w` has type `B ! Δ`.
If `h : A ! Δ ⇒ B ! Δ'` and `c : A ! Δ`, then `with h handle c` has type `B ! Δ'`.
