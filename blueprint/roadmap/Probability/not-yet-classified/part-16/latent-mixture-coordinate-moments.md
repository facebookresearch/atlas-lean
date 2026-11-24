# Latent-mixture coordinate moments

Let `Z` (latent states) and `ι`
(items) be finite, `pi : PMF Z` a latent law with no support restriction,
and `q z i ∈ [0, 1]` item curves (endpoints `0` and `1` allowed). Under
the observed law `pi.bind (fun z => localIndepPMF (q z) ..)`, the first
moment of coordinate `i` is the `pi`-mixture of the component means
`q z i`, the off-diagonal pair moment of distinct coordinates `i, j` is
the mixture of the component products `q z i * q z j`, and for distinct coordinates
`i ≠ j` the observed covariance is the finite covariance of the curves
`z ↦ q z i`, `z ↦ q z j` under the weights `(pi z).toReal`.
