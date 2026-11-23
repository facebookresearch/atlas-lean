# The Gaussian cluster response is a random-intercept model

Indexing the `m` rows by
`Fin 1 × Fin m` (one donor, `m` cells), the rows of `Y = X β + 𝟙 γ + ε` satisfy `IsRandomIntercept`
of `Domains.Biology.Omics.Pseudobulk` with donor variance `σc2` and residual variance `σw2`, so
that file's second-moment results apply to this response.
