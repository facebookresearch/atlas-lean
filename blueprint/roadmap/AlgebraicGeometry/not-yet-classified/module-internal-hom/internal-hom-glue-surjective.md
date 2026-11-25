# Internal Hom glue surjective

If `G` is a sheaf, every compatible family `(φ I)_I` of morphisms `F|_{I.Y} ⟶ G|_{I.Y}`
over the members of a cover `S` of `U` is the family of restrictions of a morphism
`F|_U ⟶ G|_U`.

This is the gluing half of the sheaf condition: the underlying sections of the family glue in
the sheaf of homs `presheafHom F.presheaf G.presheaf` to `gluedUnder`, which is upgraded to an
`O|_U`-linear morphism `gluedHom` restricting to each member of the family.
