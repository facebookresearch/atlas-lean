# Is Colimit Cokernel Cofork Of Cofiber Sequence

Let `C` have zero morphisms, a zero object, and a Waldhausen structure
without gluing. If `(f : X ⟶ Y, g : Y ⟶ Z)` is a cofiber sequence, its
quotient map `g` gives a colimit witness for the specified cokernel cofork
`CokernelCofork.ofπ g hSeq.comp_eq_zero`. This uses the supplied maps and
their zero composite, not a separately chosen cokernel object.
