# Homoplasy-matched simulation null for phylogenetic association tests

**Setting.** Microbial genome-wide association is confounded by clonal population structure and by recombination: loci and phenotypes that are both structured by the phylogeny appear associated even without a causal link. Let $\mathcal{T}$ be the reconstructed phylogeny of the sample (branch lengths $\ell_e$), $\phi$ the observed phenotype at the leaves, and, for each empirical biallelic locus, let $k$ be its number of substitutions on $\mathcal{T}$ under parsimony reconstruction; the empirical distribution of $k$ across loci is the **homoplasy distribution** $\hat\pi(k)$.

**Procedure.**

1. Simulate $N_{\mathrm{sim}}$ null loci (at least ten times the number of empirical biallelic sites). For each, draw $k \sim \hat\pi$, choose $k$ branches with probabilities proportional to $\ell_e$, place one substitution on each, and propagate states from the root to the leaves.
2. Keep the tree and the observed leaf phenotype fixed, so null loci share the population structure and the recombination-driven homoplasy of real loci but are independent of the phenotype given the tree.
3. For each association score $s$ (e.g. the terminal, simultaneous and subsequent scores), compute $s$ for all simulated loci; the threshold $t_s$ is the upper $(1 - \alpha^*)$ quantile of this null distribution, where $\alpha^*$ is the base level corrected for multiple testing over the number of loci and the number of scores (Bonferroni by default, or false discovery rate control).
4. Declare an empirical locus significant for score $s$ if its score exceeds $t_s$, with empirical $p$-value equal to the fraction of null scores at least as large.

**Properties.**

1. Under the null hypothesis that the locus evolves on $\mathcal{T}$ by the same substitution process as the simulated loci and independently of the phenotype given the tree, the empirical score is exchangeable with the simulated scores, so the empirical $p$-value is valid (up to Monte Carlo error of order $N_{\mathrm{sim}}^{-1/2}$).
2. Matching $\hat\pi$ calibrates the null for recombination: loci with many homoplasious changes are compared with null loci that also change often, which a single-substitution null would not do.

## Depends on

- [Fitch's algorithm](../../../phylogenetics/small-parsimony-problem/fitch.md)
- [Terminal, simultaneous and subsequent association scores on a phylogeny](treewas-terminal-simultaneous-and-subsequent-scores.md)

## Expansion

The homoplasy count of each empirical locus is its Fitch parsimony score on $\mathcal{T}$, and the simulated loci reproduce the distribution of these counts while placing changes at random branches weighted by length. Conditioning on the tree and phenotype makes the test a conditional randomization test: any association a null locus displays arises only from shared ancestry, so exceeding the null quantile indicates association beyond population structure. Placing substitutions proportionally to branch length assumes a molecular-clock-like substitution process along the reconstructed tree; ancestral states for scoring may be reconstructed by parsimony or by maximum likelihood.

## Sources

- Collins C, Didelot X, "A phylogenetic method to perform genome-wide association studies in microbes that accounts for population structure and recombination" (2018), Methods (simulation of null genetic data under the empirical homoplasy distribution and identification of the significance threshold), <https://doi.org/10.1371/journal.pcbi.1005958>, PMCID PMC5814097.
