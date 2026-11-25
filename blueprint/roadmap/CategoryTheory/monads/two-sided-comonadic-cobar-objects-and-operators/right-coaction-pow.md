# Right Coaction Pow

Reusable recursive iterated right-comodule coaction:
`R.functor.obj ((comonadPow G n).obj X) ⟶ R.functor.obj ((comonadPow G (n+1)).obj X)`.
Degree zero is definitionally `R.coaction.app X`; successor is definitionally
the preceding iterated coaction evaluated at `G.toFunctor.obj X`. This gives
transport-free recursive equations for the right endpoint while keeping
left-associated `comonadPow`.
