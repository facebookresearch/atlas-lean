# The gene-wise likelihood is a negative binomial regression

For a negative binomial
gene with shape `θ` and positive library sizes, the log-likelihood of the gene's counts is a
rate-free constant plus `nbLogLik θ X o y β` with the condition design `X`, offsets
`oⱼ = log (librarySize j)`, responses `yⱼ = Y g j` and coefficients `β c = log (rate g c)`.
