# Full-rank determinantal ideal of an injection

Let `K` be a field and `P,Q` free `K`-modules, with `P` finite-dimensional over `K`.
For an injective `K`-linear map `f : P →ₗ[K] Q`, the determinantal ideal of size
`dim_K P` is the unit ideal:

`f.determinantalIdeal (Module.finrank K P) = ⊤`.

The target `Q` may be infinite-dimensional, and the conclusion includes a
zero-dimensional source.
