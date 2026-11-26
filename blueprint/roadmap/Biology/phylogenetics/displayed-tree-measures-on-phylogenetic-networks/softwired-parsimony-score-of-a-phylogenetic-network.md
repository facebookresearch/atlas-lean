# Softwired parsimony score of a phylogenetic network

Let $\Sigma$ be a finite state alphabet and $W : \Sigma \times \Sigma \to \mathbb{R}_{\ge 0}$ a substitution cost with $W(\sigma, \sigma) = 0$ (the identity cost $W(\sigma_1, \sigma_2) = [\sigma_1 \ne \sigma_2]$ gives the Hamming distance). For equal-length sequences $x, y \in \Sigma^k$ put $H(x, y) = \sum_{i=1}^{k} W(x_i, y_i)$.

**Trees.** For a rooted tree $T$ whose vertices $v$ carry sequences $s_v$, the parsimony score is $\sum_{(u,v) \in E(T)} H(s_u, s_v)$. For a leaf-labelled tree $T$ and one alignment column (site) $s$, $\mathrm{TCost}(T, s)$ is the minimum of this score over all assignments of states to the internal vertices; it is the small-parsimony cost computed by Sankoff's algorithm.

**Networks.** Let $N$ be a rooted phylogenetic network leaf-labelled by a taxon set $S$, and let $\mathcal{T}(N)$ be the set of trees displayed by $N$ (obtained by keeping exactly one incoming arc at each reticulation and suppressing the resulting degree-two vertices). For an alignment of sites $s_1, \dots, s_k$ on $S$, the **parsimony score of $N$** is

$$\mathrm{NCost}(N, S) = \sum_{i=1}^{k} \min_{T \in \mathcal{T}(N)} \mathrm{TCost}(T, s_i).$$

A maximum parsimony network for the data minimizes $\mathrm{NCost}$ over networks with a prescribed number of reticulations. When $N$ is a tree, $\mathcal{T}(N) = \{N\}$ and $\mathrm{NCost}$ is the ordinary small-parsimony score. Replacing single sites by non-overlapping blocks of sites, each block forced to evolve on a single displayed tree, gives the block version of the score.

## Depends on

- [Sankoff's algorithm](../small-parsimony-problem/sankoff.md)

## Expansion

Each non-recombining site evolves along one of the trees inside the network, so the network's cost for a site is the best cost among the displayed trees, and costs add over sites. Because the minimum is taken separately for each site, $\mathrm{NCost}(N, S) \le \mathrm{TCost}(T, S)$ for every displayed tree $T$, and adding a reticulation can only lower the score; the reticulation count must therefore be penalized or fixed when the score is used for inference. Evaluating the score requires enumerating up to $2^r$ displayed trees for $r$ reticulations, which is why the comparison is exponential in the number of reticulations.

## Sources

- C. Than, D. Ruths and L. Nakhleh, "PhyloNet: a software package for analyzing and reconstructing reticulate evolutionary relationships", BMC Bioinformatics 9 (2008), 322, <https://doi.org/10.1186/1471-2105-9-322>, PMCID PMC2533029. Section "Parsimony of evolutionary networks", Definitions 1–3.
