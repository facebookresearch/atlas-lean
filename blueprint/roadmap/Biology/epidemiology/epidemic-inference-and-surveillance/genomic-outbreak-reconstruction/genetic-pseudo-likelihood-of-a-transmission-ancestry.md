# Genetic pseudo-likelihood of a transmission ancestry

In an outbreak with one pathogen sequence $s_i$ per sampled case $i$, let $\alpha_i$ be the closest sampled ancestor of case $i$ in the transmission tree and $\kappa_i \ge 1$ the number of generations of infection separating them (so $\kappa_i - 1$ intermediate cases were not sampled). Let $d(s_i, s_{\alpha_i})$ be the number of nucleotide differences between the two sequences and $\ell(s_i, s_{\alpha_i})$ the number of positions comparable between them. Assume that there is no within-host diversity (the transmitted and the sampled strain coincide), that sites mutate independently with probability $\mu \in (0,1)$ per site per generation of infection, and that reverse mutations are negligible. The genetic pseudo-likelihood of the ancestry $\alpha_i \to i$ is

$$\Omega^{1}_i = \mu^{\,d(s_i, s_{\alpha_i})} \,(1 - \mu)^{\,\kappa_i \ell(s_i, s_{\alpha_i}) - d(s_i, s_{\alpha_i})} .$$

If $\alpha_i$ has not been sequenced, the comparison moves up the chain to the nearest sequenced ancestor, with $\kappa_i$ replaced by the number of generations between the two compared sequences.

## Expansion

With $\kappa_i$ generations and $\ell$ comparable sites there are $\kappa_i \ell$ independent site-generations, of which exactly the $d$ observed differences mutated; no binomial coefficient appears because the identity of the mutated sites is observed, not just their number. Because only pairwise distances enter, the term is cheap to evaluate and every transmission event contributes independently, which is what makes Markov chain Monte Carlo over transmission trees feasible. The price is that shared ancestry along unsampled chains is ignored: when several cases descend from a common unsampled ancestor they are no longer conditionally independent, so the product of case terms is a composite (pseudo-)likelihood. Sites under strong selection, such as drug-resistance positions, violate the neutral independent-sites assumption and should be removed first.

## Sources

- Jombart T, Cori A, Didelot X, Cauchemez S, Fraser C, Ferguson N. Bayesian reconstruction of disease outbreaks by combining epidemiologic and genomic data. *PLoS Computational Biology* 10:e1003457 (2014), Methods, "Posterior distribution and full likelihood", "Genetic pseudo-likelihood" and "Epidemiological pseudo-likelihood", equations (3)–(7). DOI <https://doi.org/10.1371/journal.pcbi.1003457>. PMCID PMC3900386.
