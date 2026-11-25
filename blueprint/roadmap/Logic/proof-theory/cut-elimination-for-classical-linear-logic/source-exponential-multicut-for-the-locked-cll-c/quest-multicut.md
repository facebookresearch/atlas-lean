# Exponential multicut against replicated question marks

Assume that cut is admissible in the cut-free system CF for every proposition of smaller size
than `!a`. Let `Γ` be a list of why-not propositions (each of the form `ʔb`), `p` a cut-free
proof of `⊢ a, Γ`, and `q` a cut-free proof of `⊢ ʔ(a⫠), …, ʔ(a⫠), Δ` with `n ≥ 0` selected copies
of `ʔ(a⫠)`. Then `⊢ Γ, Δ` has a cut-free proof.

Since `Γ` consists of why-not propositions, promotion turns `p` into a proof of `⊢ !a, Γ`; the
construction eliminates the `n` cuts of `!a` against the selected copies of `ʔ(a⫠)` at once, by
induction on `q`.
