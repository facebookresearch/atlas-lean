# Raw Operations

For a stack `R` over `S`, identity and composition for morphisms of charts of `R` (`RawHom`: a
morphism of stacks with an invertible triangle over `R`). For each chart there is an identity
morphism whose underlying morphism of stacks is the identity and whose triangle has identity
components (`identity`). For composable `f` and `g` there is a composite (`compose`) whose
underlying morphism of stacks is the composite and whose triangle has, at each object `x` over
`T`, the component of the triangle of `g` at `f(x)` followed by the component of the triangle of
`f` at `x`.
