# Étale base change of Néron models

Let `φ : Spec R' ⟶ Spec R` be smooth (for instance
étale), with `ψ : Spec K' ⟶ Spec K` making the square of generic points a pullback, that is,
`K' = R' ⊗_R K`. If `M` is a Néron model of `A` over `R`, then its base change `M.model ×_R R'`,
with the identification of its generic fibre with `A ×_K K'` induced by that of `M`
(`genericBaseChangeIso`), is a Néron model of `A ×_K K'` over `R'`.

This is Lichtenstein, *Néron models*, Proposition 1.4.3 with its proof, pp. 5–6, stated there
for an integral domain `R'` étale over a Dedekind domain `R`; here `R'` is any domain with
fraction field `K'`, smoothness of `φ` replaces étaleness, and `A` is any `K`-scheme.
