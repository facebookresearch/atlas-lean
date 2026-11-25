# Gen Last Fst

Iterated functoriality drops the generalized tail tuple entry.

Stable API for `powTupleGen`: mapping the tail action preserves the `n`-tuple
(`genMapFst`) while the outermost `snoc` layer becomes the tail: peel one
`powTupleGen_succ_fst` layer and close the init with `Fin.init_snoc`.
