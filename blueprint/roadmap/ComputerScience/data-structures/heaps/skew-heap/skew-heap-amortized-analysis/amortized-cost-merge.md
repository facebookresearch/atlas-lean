# Amortized Cost merge

Ch. 19, equation (19.1): the amortized running time of a
one-argument operation is `A_f s = T_f s + Φ (f s) - Φ s`. For a
two-argument operation (e.g. `merge`), the analogue given in Ch. 19
is `A_g s₁ s₂ = T_g s₁ s₂ + Φ (g s₁ s₂) - (Φ s₁ + Φ s₂)`.
The framework's `acost` is exactly this definition, with `cost`
in place of `T` (the framework's `cost` for skew heaps is `T_merge`
for `merge`, and `T_insert + 1` / `T_delMin + 1` for insert /
delMin — the `+1` is Isabelle's framework `cost`, see the comment on
`skewCost`; `a_insert` / `a_delMin` are stated with `T_insert` /
`T_delMin` as in the analysis file). The three lemmas below state
`acost` for the skew operations in the form (19.1).
