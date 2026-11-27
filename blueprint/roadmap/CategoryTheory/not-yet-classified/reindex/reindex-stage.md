# Reindex Stage

Contravariant reindexing of bundled stages: a simplex map `a ⟶ b`
gives `Stage C b.len ⟶ Stage C a.len`, via the existing full-subcategory
lift. Precomposition itself is direct `⋙` / `whiskerLeft` reuse; the
`IsStage` proof below reuses the original `diag_isZero` and
`cofiber_triple` after transporting `diag` / `horiz` / `vert` along the
indexing functor.
