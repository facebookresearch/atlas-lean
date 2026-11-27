# Axiom case of the exponential multicut

The axiom case of the exponential multicut. Let `Γ` be a list of why-not propositions (each of
the form `ʔb`) and `p` a cut-free proof of `⊢ a, Γ`. If the conclusion `c, c⫠` of an axiom is
`n` selected copies of `ʔ(a⫠)` together with `Δ`, then `⊢ Γ, Δ` has a cut-free proof. There are
two cases, since `c` and `c⫠` cannot both be copies:

- `n = 1`: one of `c`, `c⫠` is the copy of `ʔ(a⫠)` and the other is `!a`, so `Δ` is `!a`; promotion
  turns `p` into a proof of `⊢ !a, Γ`.
- `n = 0` and `Δ` is `c, c⫠`: weakening the axiom by the propositions of `Γ` gives `⊢ Γ, c, c⫠`.
