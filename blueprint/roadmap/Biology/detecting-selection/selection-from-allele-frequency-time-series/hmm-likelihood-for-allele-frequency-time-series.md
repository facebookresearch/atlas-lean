# Hidden Markov likelihood for allele-frequency time series

This node covers likelihood inference of effective population size and selection coefficient from
allele frequencies sampled at several times at one diallelic locus. Bollback, York and Nielsen (2008)
compute transition probabilities of the allele frequency by a numerical solution of the diffusion
process and assume independent binomial sampling from it at each sampling time, which gives a hidden
Markov likelihood. The corresponding finite-population model replaces the diffusion transition by the
Wright–Fisher chain with selection on the possible allele counts.

## Expansion

A sound expansion states the likelihood of the finite-population hidden Markov model as a forward
recursion over allele counts, proves its continuity in the selection coefficient and the existence of a
maximum-likelihood estimate over a compact interval, and treats the diffusion approximation and any
consistency statement as separate pages with their own regime.

## Sources

- J. P. Bollback, T. L. York and R. Nielsen, "Estimation of $2N_e s$ from temporal allele frequency
  data", Genetics 179 (2008), 497–502, <https://doi.org/10.1534/genetics.107.085019>.
