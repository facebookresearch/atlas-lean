# Equiv Of Ring Equiv comp apply

For rings `R, S, T : Type u`, ring equivalences `e : R ≃+* S` and
`e′ : S ≃+* T`, and `x : K1 R`, transport along `e.trans e′` sends `x` to
`K1.equivOfRingEquiv e′ (K1.equivOfRingEquiv e x)` in `K1 T`.
