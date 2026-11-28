# Trans-dimensional proposals for ancestral recombination graphs

Samplers of ancestral recombination graphs from their posterior move between graphs with different numbers of recombination or conversion events, so the number of event times, and hence the dimension of the state, changes between states. In Vaughan et al.'s sampler for the ClonalOrigin model (2017, Appendix), each step draws a proposal kernel $q_w$ from a fixed weighted family and accepts $x'$ with probability

$$\alpha_w(x' \mid x) = 1 \wedge \frac{\pi(x')}{\pi(x)}\, h_w(x' \mid x)$$

(equation (A1)), where the Hastings–Green factor $h_w$ is determined by the proposal and makes the chain reversible; among the operators, Add/Remove moves add or delete a conversion that mirrors an existing clonal-frame edge, or a pair of conversions forming a detour, each chosen with probability $1/2$, and each operator is given with its factor. In ARGweaver (Rasmussen et al. 2014), re-threading a single sequence is an exact Gibbs step under the discretized model, but re-threading an internal subtree is not: the number of ways of removing internal branches depends on the current graph, so the Hastings ratio differs from one and a general Metropolis–Hastings step with rejection is used, with acceptance rates of about 40% on typical human data. In SINGER, sub-graph pruning and re-grafting proposals are accepted by a Metropolis–Hastings rule whose acceptance probability, assuming the threading samples approximately from the posterior, is typically much higher than that of previous proposals (Deng, Nielsen and Song 2025, Methods).

## Expansion

1. State spaces of graphs with varying numbers of events, and reference measures on each dimension.
2. The Hastings–Green acceptance rule (A1) for a proposal between dimensions, with dimension matching and the Jacobian of the change of variables.
3. The Add/Remove operators of Vaughan et al.'s sampler for the ClonalOrigin model and their factors, and reversibility of each with respect to the posterior.
4. The subtree re-threading step of ARGweaver as a Metropolis–Hastings step, with its Hastings ratio.
5. The role of the approximations in the target (time discretization, sequentially Markov prior, clonal-frame restriction).

## Sources

- T. G. Vaughan, D. Welch, A. J. Drummond, P. J. Biggs, T. George and N. P. French, Inferring ancestral recombination graphs from bacterial genomic data, Genetics 205 (2017), 857–870, Appendix (equation (A1) and the Add/Remove operators). <https://doi.org/10.1534/genetics.116.193425>
- M. D. Rasmussen, M. J. Hubisz, I. Gronau and A. Siepel, Genome-wide inference of ancestral recombination graphs, PLoS Genet. 10 (2014), e1004342, section on subtree threading. <https://doi.org/10.1371/journal.pgen.1004342>
- Y. Deng, R. Nielsen and Y. S. Song, Robust and accurate Bayesian inference of genome-wide genealogies for hundreds of genomes, Nat. Genet. 57 (2025), 2124–2135, Methods (SGPR). <https://doi.org/10.1038/s41588-025-02317-9>
