# Local morphism data on a family of opens

Let `X : TopCat.{u}`, `R` be a ring sheaf of carrier universe `u`, `F,G` module sheaves of
carrier universe `u`, and `U : ι → Opens X` with `ι : Type v`. `CoverHomData F G U` consists
of `R(V)`-linear maps `F(V) → G(V)` for every chart `i` and `V ≤ U_i`, natural under
inclusions of subopens and equal whenever `V` lies below two charts. The fields are
`localHom`, `naturality`, and `agree`.
