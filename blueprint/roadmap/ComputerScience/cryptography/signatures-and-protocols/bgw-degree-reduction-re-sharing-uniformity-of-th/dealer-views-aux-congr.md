# Joint dealer views depend only on the listed dealers

Let `Party` have decidable equality. If two families of per-dealer view
distributions `f₁` and `f₂` agree on every dealer in the list `l`, then
`dealerViewsAux f₁ l g = dealerViewsAux f₂ l g` for every base matrix `g`.
