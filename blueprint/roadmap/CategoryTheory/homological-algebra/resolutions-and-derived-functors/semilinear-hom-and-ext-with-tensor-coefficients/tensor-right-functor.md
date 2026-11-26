# Tensoring on the right with a fixed semimodule

For a commutative semiring `S : Type s` and `U : SemimoduleCat.{vU} S`, the functor
`SemimoduleCat.{vN} S → SemimoduleCat.{max vN vU} S` sends `N` to `N ⊗[S] U` and a linear map
`f` to `f.rTensor U`. The coefficient and tensor-factor carrier universes are independent.
