# Tensor Hom f eq graded

A complex tensor-map component is the corresponding graded tensor map.

Rewrite direction: from `(tensorHom f g).f j` to the graded-object
`tensorHom` at `j`.  This is the one-level peeling rewrite used before
`GradedObject.Monoidal.tensorHom_apply_heq`; the test module pins that exact
two-step pattern.
