# Generating sections restricted along a base arrow

Let `(C,J,R)` be a ringed site with binary products and pullbacks in `C`, and weak additive
sheafification with the locally-bijective comparison on the base and every slice. For `f : X →
Y`, a module sheaf `M`, and generating sections `G` of `M.over Y`,
`GeneratingSections.overRestrict f G` gives generating sections of `M.over X`. It transports
`G` along `overMap R f` and the canonical over-functor comparison, retaining the index set
`G.I`.
