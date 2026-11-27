# Is Cofiber Sequence Of Cofibration And Cokernel

Let `C` have zero morphisms, a zero object, and a Waldhausen structure
without gluing. For a cofibration `f : X ⟶ Y` and a supplied map
`g : Y ⟶ Z`, assume `w : f ≫ g = 0` and a colimit witness
`hg : IsColimit (CokernelCofork.ofπ g w)` for this particular cofork.
Then `(f, g)` is a cofiber sequence through the selected zero object.
Existence of some other cokernel, without a witness for `g`, is not the
hypothesis.
