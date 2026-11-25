# `moduleTensor` and the monoidal tensor product

The sheaf tensor product
`MathlibExt.AlgebraicGeometry.SchemeModulesTensor.moduleTensor X L M` of the line-bundle interfaces
is isomorphic to `L ⊗ M` for the monoidal structure on `X.Modules`. Both sheafify the presheaf
tensor product `L.val ⊗ M.val`; this is `Scheme.Modules.tensorIsoSheafify L M`.
