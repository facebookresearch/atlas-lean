# Glued value of a section

Let `F,G` be module sheaves on `(X,R)`, `U` an open cover, and `D : CoverHomData F G U`. For
`V∈Opens X` and `s∈F(V)`, `gluedApp D hU V s` is the section of `G(V)` whose restrictions to
`V ∩ U_i` are the local images `D.localHom i (V ∩ U_i)(s|_{V∩U_i})`. The target sheaf's
separatedness makes this section unique.
