# Stars and bars

**Stars and bars** for the Einstein solid: there are `(N + q - 1).choose q` ways to distribute
`q` indistinguishable quanta among `N` oscillators, that is functions `f : Fin N → ℕ` with
`∑ i, f i = q`. The count transports Mathlib's `Sym.card_sym_eq_choose` along
`Sym.equivNatSumOfFintype`.
