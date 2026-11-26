# Grassmannian Adjoin

Let `Gr` be a scheme over `Spec R` that represents the Grassmannian functor
`A ↦ Module.Grassmannian A (A ⊗[R] M) k` naturally in `A` (`pt`, `hpt`), and let `V x` be
the open of `Gr` through which exactly the points of the chart at `x` factor (`hVchart`).
If `g : ι → M` spans `M` and `N` is a point over `S` whose representing map
`Spec S ⟶ Gr` is an open immersion with image `V x`, then the chart coordinates of the
`g a`, the coefficients `c i` with `∑ j, c j • N.mkQ (1 ⊗ₜ x j) = N.mkQ (1 ⊗ₜ g a)`,
generate `S` as an `R`-algebra.
