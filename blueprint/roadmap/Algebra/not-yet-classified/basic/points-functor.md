# Points Functor

The contravariant functor assigning to a commutative Hopf algebra its group-valued
functor of points.

A coordinate Hopf algebra `H` is sent to the functor `A ↦ WithConv (H →ₐ[R] A)`. A morphism
`φ : H ⟶ K` is sent contravariantly to the natural transformation that pre-composes
`K`-points by `φ`.
