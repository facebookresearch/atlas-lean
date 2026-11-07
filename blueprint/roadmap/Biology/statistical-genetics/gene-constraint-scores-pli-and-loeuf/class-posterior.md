# Posterior class probability in the Poisson mixture

The posterior probability of class `c` for a gene with `o` observed and `E` expected LoF
variants, in the Poisson mixture with prior weights `w` and class rates `rate`:
`w_c P(o | rate_c E) / ∑_{c'} w_{c'} P(o | rate_{c'} E)`. pLI is this at the class with the smallest
rate.
