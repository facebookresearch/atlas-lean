# Conv leibniz

Leibniz rule for the graded convolution product: differentiating
`f ⋆ g` differentiates the left factor first, then the right factor with
the Koszul sign `(-1) ^ m`.

The two right-hand summands are stated as explicit `Cochain.comp`
composites landing in degree `m + n + 1` (via explicit degree proofs),
i.e. as `conv (δ f) g` and `conv f (δ g)` up to degree transport. The
proof pushes `δ` inward with the pinned `δ_comp` (the `ofHom` comultiplication
and multiplication are cycles by `δ_ofHom`), then closes at components with
`tensorCochain_δ_v`.
