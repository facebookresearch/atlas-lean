# Modules Linear

The canonical linear structure on module sheaves over a scheme over `R`.

This is not an instance: the action depends on the structure morphism `X.hom`,
which `X.left.Modules` does not record, so two `R`-scheme structures on one
scheme give two linear structures. Install it locally, for instance with
`local instance : Linear R X.left.Modules := modulesLinear R X`.
