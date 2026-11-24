# Unop Obj Iso R

The `unopFunctor`-image of the op'd right-endpoint complex is the original
cocomplex (definitionally). Stated with `unopFunctor.obj` (rather than `.op`
followed by `.unop`) so all endpoint shapes are syntactically
`(down ℕ).symm`, keeping `rw`-matching sound (the `.unop` roundtrip shape
`((up ℕ).symm).symm` is only default-transparency defeq).
