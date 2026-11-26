# From integer power series to Laurent series over $K$

The ring map `ℤ⟦q⟧ → K((q))` that
first changes coefficients along `Int.castRingHom K`, giving `ℤ⟦q⟧ → K⟦q⟧`, and then includes
power series into Laurent series; it sends `q` to `q`. It is not an embedding in general: for
`K = ZMod 5` the nonzero constant series `5` maps to `0`. It is injective exactly when
`Int.castRingHom K` is, that is, when `K` has characteristic zero.
