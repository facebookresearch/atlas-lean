# Shrinking local generator data preserves finite type

Let `(D,K)` be a site, `S : Sheaf K RingCat.{u}`, and assume weak additive sheafification and
the locally-bijective comparison on every slice `K.over X`. For a module sheaf `M` and local
generator data `q`, if every chart's generating family is finite (`q.IsFiniteType`), then
`q.shrink.IsFiniteType`. Each shrunk chart uses a selected generating family from `q`.
