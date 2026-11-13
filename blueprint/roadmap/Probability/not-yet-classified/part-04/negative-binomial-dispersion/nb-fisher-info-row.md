# Nb Fisher Info Row

The expected (Fisher) information of one count with covariate row `x` and linear predictor
`η`: `[[F x xᵀ, 0], [0, nbShapeFisherInfo θ η]]` with `F = nbFisherWeight θ η`. It is block
diagonal (`hasSum_nbObsInfoRow`).
