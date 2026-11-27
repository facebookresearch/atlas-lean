# Of Retract

An oplax monoidal structure on a retract `G` of an oplax monoidal functor `F`, given by
`e : Retract G F`, provided the idempotent `e.r ≫ e.i` of `F` does not change the counit `η F`
and the comultiplication `δ F` followed by `e.r ⊗ e.r`.  The counit of `G` is `e.i ≫ η F`
(`CategoryTheory.Functor.OplaxMonoidal.ofRetract_η`) and its comultiplication is
`e.i ≫ δ F ≫ (e.r ⊗ e.r)` (`CategoryTheory.Functor.OplaxMonoidal.ofRetract_δ`).
