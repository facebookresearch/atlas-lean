# Iso Of Quasi Iso At naturality

Naturality square for `isoOfQuasiIsoAt`.

For a commuting square `u ≫ f' = f ≫ v` in which `f` and `f'` are
quasi-isomorphisms in degree `i`, the homology maps of the vertical arrows
commute with the induced homology isomorphisms of the horizontal arrows:

`homologyMap u ≫ (isoOfQuasiIsoAt f').hom = (isoOfQuasiIsoAt f).hom ≫ homologyMap v`.

The proof applies `homologyMap` to the commuting square and uses the
functoriality `homologyMap_comp` together with
`(isoOfQuasiIsoAt _ _).hom = homologyMap _ _`.
