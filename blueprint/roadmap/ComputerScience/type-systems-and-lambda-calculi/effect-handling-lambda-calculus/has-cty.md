# Typing of computations

`HasCTy sig Γ c C` is the judgment `Γ ⊢ c : C` of Pretnar 2015,
Fig. 6, with the generic effect `op o v` in place of `op(v; y. c)`: `return v` has type
`A ! Δ` for every `Δ`; `op o v` has type `B_o ! Δ` when `o ∈ Δ` and `v : A_o`; both
computations of `do` share the effect set; an application takes its effect set from the
function type; and `with h handle c` has the output type of the handler `h`.
