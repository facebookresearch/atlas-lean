# Internal Hom glue injective

If `G` is a sheaf, a morphism `F|_U ⟶ G|_U` of `O|_U`-modules is determined by its
restrictions to the members of a cover `S` of `U`.

This is the separation half of the sheaf condition on `G|_U`: the sheaf `G` relocalizes to a
sheaf `(Over.forget U).op ⋙ G.presheaf` for the slice topology `J.over U`, two morphisms agreeing
on the members of `S` agree at every slice object whose structure map lies in `S`, and the cover
`S` pulled back along the structure map of an object `W` of `Over U` is a cover of `W` for
`J.over U`, on which `Presheaf.IsSheaf.hom_ext` applies.
