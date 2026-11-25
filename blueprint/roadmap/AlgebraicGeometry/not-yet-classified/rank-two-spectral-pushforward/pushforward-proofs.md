# Pushforward Proofs

Data and conditions for pushing rank-one sheaves on the spectral fibre over an `Ω`-point `s` of
the Hitchin base forward to Higgs bundles. Write `π` for the projection from the spectral fibre
over `s` to `C × Spec Ω`, and `K` for the pullback of the canonical line bundle of `C` to
`C × Spec Ω`. The fields are: a comparison of pullback along `π` with tensor products (`tensor`);
`K` is a line bundle (`line`); and, for every rank-one torsion-free sheaf `E` on the spectral fibre
of degree `2g - 1`, where `g` is the genus of `C` (an object of `RankOneSheaves`), the
projection-formula map `π_* E ⊗ K ⟶ π_* (E ⊗ π^* K)` is an isomorphism (`formula`), `π_* E` is a
vector bundle of rank two (`rank`), and the Higgs bundle on `π_* E` whose field is the pushforward
of multiplication by the tautological section followed by the inverse of the projection-formula
map is admissible, that is, stable of rank two and degree one on every geometric fibre (`stable`),
and lies over `s` under the Hitchin map (`characteristic`); finally, the pushforward of every
isomorphism `E ≅ E'` of such sheaves commutes with the Higgs fields (`arrows`).
