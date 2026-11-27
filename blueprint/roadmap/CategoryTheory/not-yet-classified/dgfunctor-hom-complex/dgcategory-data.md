# Explicit Hom-complex data

**Explicit Hom-complex data** for a differential graded category over `R` on the objects
`C`: a Hom complex `hom X Y` for every pair of objects, bilinear composition
`comp p q n h : (hom X Y).X p →ₗ[R] (hom Y Z).X q →ₗ[R] (hom X Z).X n` for `p + q = n`, in
Mathlib's enriched factor order, and identities `id X` of degree zero, satisfying the graded
Leibniz rule, associativity, and the unit laws on homogeneous elements.  Such data determines the
differential graded category `MathlibExt.DGSource.DGCategoryData.toDGCategory`.
