# Site likelihoods under discrete rate heterogeneity

Let a site evolve on a tree with branch lengths $t$ at a rate drawn from a discrete distribution: rate $r_k > 0$ with weight $w_k \ge 0$, $\sum_k w_k = 1$,
normalized so that $\sum_k w_k r_k = 1$, independently of everything else. Conditioning on the rate category, the site likelihood is

$$L_{\mathrm{site}}(t) = \sum_k w_k\, L_{\mathrm{site}}(r_k t),$$

where each $L_{\mathrm{site}}(r_k t)$ is the likelihood with all branch lengths scaled by $r_k$, computed by one [pruning pass](prune-eq-brute-lik.md); for independent sites the alignment
likelihood is the product of these mixture site likelihoods. With one category it is the homogeneous model, and the mean-rate
normalization keeps branch lengths in expected substitutions per site.

## Depends on

- [Felsenstein's pruning algorithm computes the likelihood conditioned on the root state](prune-eq-brute-lik.md)

## Sources

- Z. Yang, "Maximum likelihood phylogenetic estimation from DNA sequences with variable rates over sites: approximate methods", Journal of Molecular Evolution 39 (1994), 306–314, <https://doi.org/10.1007/BF00160154>.
