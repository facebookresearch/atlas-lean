# Op Proj Left

The op'd left-endpoint resolution, ascribed to the `ProjectiveResolution`
type with the exact baked instances (`Abelian.hasZeroObject`,
`Preadditive.preadditiveHasZeroMorphisms`) and object (`S.op.X₁`) that
`HorseshoeData`'s `P₁` slot carries. (Without ascription, `rw`/`simp` fail:
`injectiveResolutionOpProj` bakes `hasZeroMorphismsOpposite` over
`op S.X₃`, which is only default-transparency defeq to the slot type, while
tactics check at reducible transparency.)
