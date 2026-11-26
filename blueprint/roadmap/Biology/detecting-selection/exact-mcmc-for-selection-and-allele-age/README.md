# Exact MCMC for selection and allele age

Bayesian inference of selection coefficients and allele age from allele-frequency time series (for example ancient DNA) usually needs the intractable Wright–Fisher transition density. Augmenting the state space with the latent frequencies and the skeleton points of an exact rejection sampler makes the joint density explicit, so an MCMC chain targets the exact posterior with no discretization error.

- [Skeleton-augmented posterior for Wright–Fisher time series](skeleton-augmented-posterior-for-wright-fisher-time-series.md)
