# Likelihood of a selection coefficient from sampled genealogies (CLUES)

Stern, Wilton and Nielsen (2019) approximate the full likelihood of a selection coefficient $s$ at a site from sequence data by treating the ancestral recombination graph as a latent variable. The allele-frequency trajectory of the selected allele is marginalized by a dynamic program of hidden-Markov type, whose hidden states are allele frequencies and whose emissions are the coalescence events of the local genealogy; the source describes it as a time-inhomogeneous hidden Markov model, whose emission space changes with time, to which the usual hidden Markov model algorithms apply. Genealogies are sampled under a neutral prior and reweighted by importance sampling, so that the likelihood can be evaluated at any $s$ from a single set of samples (Introduction and Methods).

## Depends on

- [Mean age of an allele at a given frequency](../../../population-genetics/diffusion-theory/allele-age-and-the-maruyama-effect/mean-age.md)
- [Mean age of a neutral allele](../../../population-genetics/diffusion-theory/allele-age-and-the-maruyama-effect/mean-age-zero.md)
- [The Maruyama effect](../../../population-genetics/diffusion-theory/allele-age-and-the-maruyama-effect/mean-age-lt.md)

## Expansion

1. The trajectory model for the selected allele and the conditional law of the coalescence times in the two allelic backgrounds given the trajectory.
2. The forward–backward marginalization of the trajectory, with the time-inhomogeneous emission space.
3. Importance sampling of genealogies drawn under the neutral prior and the resulting likelihood estimate as a function of $s$.
4. The distribution of the age of a mutation carried by $b$ of $n$ sampled genes in a fixed genealogy, by placing the mutation on the branches that subtend exactly $b$ genes, as a separate statement.

## Sources

- A. J. Stern, P. R. Wilton and R. Nielsen, An approximate full-likelihood method for inferring selection and allele frequency trajectories from DNA sequence data, PLoS Genet. 15 (2019), e1008384, Introduction and Methods. <https://doi.org/10.1371/journal.pgen.1008384>
