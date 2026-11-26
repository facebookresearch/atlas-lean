# Softwired parsimony score of a phylogenetic network

Let $\Sigma$ be a finite state alphabet and $W : \Sigma \times \Sigma \to \mathbb{R}_{\ge 0}$ a substitution cost with $W(\sigma, \sigma) = 0$ (the identity cost $W(\sigma_1, \sigma_2) = [\sigma_1 \ne \sigma_2]$ gives the Hamming distance). For equal-length sequences $x, y \in \Sigma^k$ put $H(x, y) = \sum_{i=1}^{k} W(x_i, y_i)$.

**Trees.** For a rooted tree $T$ whose vertices $v$ carry sequences $s_v$, the parsimony score is $\sum_{(u,v) \in E(T)} H(s_u, s_v)$. For a leaf-labelled tree $T$ and one alignment column (site) $s$, $\mathrm{TCost}(T, s)$ is the minimum of this score over all assignments of states to the internal vertices; it is the small-parsimony cost computed by Sankoff's algorithm.

**Networks.** Let $N$ be a rooted phylogenetic network whose leaves are labelled bijectively by a taxon set $X$. A *switching* of $N$ keeps exactly one incoming arc at each reticulation $v$ and deletes the others; there are $\prod_v \mathrm{indeg}(v)$ switchings, the product over reticulations ($2^r$ when all $r$ reticulations have in-degree $2$). A switching can leave unlabelled vertices of out-degree $0$ (a vertex whose children are all reticulations that kept another parent), so the displayed tree of a switching is obtained by repeatedly deleting unlabelled out-degree-$0$ vertices and then suppressing in-degree-$1$ out-degree-$1$ vertices and an out-degree-$1$ root. Its leaf set is exactly $X$. Let $\mathcal{T}(N)$ be the set of trees displayed by $N$ in this sense. For an alignment $\mathcal{A} = (s_1, \dots, s_k)$ of $k$ sites, each site $s_i : X \to \Sigma$ assigning a state to every taxon, the **parsimony score of $N$** is

$$\mathrm{NCost}(N, \mathcal{A}) = \sum_{i=1}^{k} \min_{T \in \mathcal{T}(N)} \mathrm{TCost}(T, s_i).$$

The alignment $\mathcal{A}$ is the argument of the score; the taxon set $X$ only labels the leaves. A maximum parsimony network for the data minimizes $\mathrm{NCost}$ over networks with a prescribed number of reticulations. When $N$ is a tree, $\mathcal{T}(N) = \{N\}$ and $\mathrm{NCost}$ is the ordinary small-parsimony score. Replacing single sites by non-overlapping blocks of sites, each block forced to evolve on a single displayed tree, gives the block version of the score.

## Depends on

- [Sankoff's algorithm](../small-parsimony-problem/sankoff.md)

## Proof depends on

- [Sankoff's cost is attained](../small-parsimony-problem/exists-edge-cost-eq-sankoff.md)

## Expansion

Each non-recombining site evolves along one of the trees inside the network, so the network's cost for a site is the best cost among the displayed trees, and costs add over sites. Because the minimum is taken separately for each site, $\mathrm{NCost}(N, \mathcal{A}) \le \sum_{i} \mathrm{TCost}(T, s_i)$ for every displayed tree $T$. Adding a reticulation never increases the score, since every tree displayed before is still displayed; the reticulation count must therefore be penalized or fixed when the score is used for inference. Evaluating the score by direct enumeration visits at most $\prod_v \mathrm{indeg}(v)$ switchings, which is exponential in the number of reticulations; this is one algorithm, not a lower bound on the cost of computing the score.

## Sources

- C. Than, D. Ruths and L. Nakhleh, "PhyloNet: a software package for analyzing and reconstructing reticulate evolutionary relationships", BMC Bioinformatics 9 (2008), 322, <https://doi.org/10.1186/1471-2105-9-322>, PMCID PMC2533029. Section "Parsimony of evolutionary networks", Definitions 1–3, and the network characterization via displayed trees.
