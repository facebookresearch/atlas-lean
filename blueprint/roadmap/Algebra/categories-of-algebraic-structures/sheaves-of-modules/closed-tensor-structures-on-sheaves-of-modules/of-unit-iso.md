# Of Unit Iso

Unit comparison for restriction, from the lifted monoidal structure:
`restrictSheaf.obj 𝟙 ≅ 𝟙`. This is the canonical unit comparison (the symmetry
of `Functor.Monoidal.εIso` for the `ofMonoidal` instance). Together with
`ofTensorIso` this is the interface later dual arguments need (e.g. pushing an
evaluation `L ⊗ dual L ⟶ 𝟙` through restriction).
