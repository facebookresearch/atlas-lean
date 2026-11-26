# Epidemiological pseudo-likelihood with unobserved intermediate cases

Keep the setting of the genetic pseudo-likelihood, and let $t_i$ be the collection date of case $i$, $T^{\mathrm{inf}}_i$ its (unobserved, augmented) infection date, $f$ the distribution of the delay from infection to collection, $w$ the generation-time distribution and $w^{(\kappa)} = w * \cdots * w$ its $\kappa$-fold convolution, and $\pi \in (0, 1]$ the probability that a case is sampled. The epidemiological pseudo-likelihood of case $i$ is

$$\Omega^{2}_i = f\bigl(t_i - T^{\mathrm{inf}}_i\bigr) \; w^{(\kappa_i)}\bigl(T^{\mathrm{inf}}_i - T^{\mathrm{inf}}_{\alpha_i}\bigr) \; \pi (1 - \pi)^{\kappa_i - 1},$$

where the last factor is the negative-binomial probability $\mathrm{NB}(1 \mid \kappa_i - 1, \pi)$ of one sampled case after $\kappa_i - 1$ unsampled ones (a geometric law). The full pseudo-likelihood of the sequences, collection dates, ancestries $\alpha$, generation numbers $\kappa$ and infection dates is

$$\prod_i \Omega^{1}_i \, \Omega^{2}_i,$$

with the index case contributing only its collection-delay term, and the joint posterior of ancestries, infection dates, $\mu$ and $\pi$ is proportional to this product times their prior.

## Depends on

- [Genetic pseudo-likelihood of a transmission ancestry](genetic-pseudo-likelihood-of-a-transmission-ancestry.md)

## Expansion

The three factors say, in turn, that the sample was collected a plausible time after infection, that the infection of $i$ followed that of its sampled ancestor by the sum of $\kappa_i$ independent generation times, and that exactly $\kappa_i - 1$ links of the chain were missed. Allowing $\kappa_i > 1$ is what lets the method reconstruct incompletely sampled outbreaks, and the geometric factor makes long unobserved chains costly unless the sampling proportion $\pi$ is small. The distributions $f$ and $w$ are assumed known, which makes the method less suited to pathogens with long asymptomatic carriage. Imported cases are not modelled explicitly: a preliminary run flags cases whose genetic log-likelihood is an outlier (more than five times the average influence) and their ancestry is set to unknown in the final run. Simulations recovered 70–90% of true ancestries in most settings and showed that without genetic information the transmission tree is very hard to infer.

## Sources

- Jombart T, Cori A, Didelot X, Cauchemez S, Fraser C, Ferguson N. Bayesian reconstruction of disease outbreaks by combining epidemiologic and genomic data. *PLoS Computational Biology* 10:e1003457 (2014), Methods, "Posterior distribution and full likelihood", "Genetic pseudo-likelihood" and "Epidemiological pseudo-likelihood", equations (3)–(7). DOI <https://doi.org/10.1371/journal.pcbi.1003457>. PMCID PMC3900386.
