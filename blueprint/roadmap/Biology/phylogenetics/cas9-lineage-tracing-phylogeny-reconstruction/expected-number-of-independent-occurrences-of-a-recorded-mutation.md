# Expected number of independent occurrences of a recorded mutation

**Model.** A lineage grows by $h$ rounds of synchronous binary division, so the lineage tree is a full binary tree with $n = 2^h$ leaves and $2^d$ nodes at depth $d$. Along each edge, an unedited target site mutates with probability $p \in (0, 1)$, independently across edges and sites; given a mutation it takes a specified state $s$ with probability $q$. Mutations are irreversible, so a site that has mutated never mutates again. Let $X$ be the number of edges of the tree on which the site acquires state $s$ (independent occurrences, i.e. homoplasy when $X \ge 2$).

**Claim.** The probability that the edge into a node at depth $d$ carries the mutation to $s$ is $pq(1 - p)^{d - 1}$, and

$$\mathbb{E}(X) = \sum_{d = 1}^{h} 2^d \, pq \, (1 - p)^{d - 1} = \frac{2pq\,\bigl((2 - 2p)^h - 1\bigr)}{1 - 2p} \qquad (p \ne \tfrac12),$$

with $\mathbb{E}(X) = 2pqh = qh$ when $p = \frac12$. Consequently:

- if $p > \frac12$, $\mathbb{E}(X) \le \dfrac{2pq}{2p - 1}$ for every $n$;
- if $p = \frac12$, $\mathbb{E}(X) = O(\log n)$;
- if $p < \frac12$, $\mathbb{E}(X) = O\bigl(n^{\log_2(2 - 2p)}\bigr)$.

For fixed $h$, $\mathbb{E}(X)$ is proportional to $q$ and, as a function of $p$, rises and then falls: rare mutation leaves little to repeat, while frequent mutation edits the site near the root and leaves few unedited lineages.

## Expansion

The edge into a depth-$d$ node carries the mutation exactly when the site stays unedited on the $d - 1$ ancestral edges, probability $(1 - p)^{d - 1}$, and then mutates to $s$, probability $pq$. Linearity of expectation over the $2^d$ edges at each depth gives the geometric sum $2pq \sum_{d=1}^{h} (2 - 2p)^{d - 1}$. Writing $(2 - 2p)^h = n^{\log_2(2 - 2p)}$ gives the three regimes. The source also bounds $\operatorname{Var}(X)$ by summing $\Pr(\text{both edges mutate}) = p^2 q^2 (1 - p)^{d + l + k}$ over pairs of edges whose lowest common ancestor is at depth $d$, obtaining a variance bounded in $n$ for $p > \frac12$ and $O(\log^3 n)$ for $p = \frac12$. The calculation supports splitting on frequent mutations first: in realistic regimes, mutations seen in many cells are likely to have arisen few times.

## Sources

- M. G. Jones, A. Khodaverdian, J. J. Quinn, M. M. Chan, J. A. Hussmann, R. Wang, C. Xu, J. S. Weissman and N. Yosef, "Inference of single-cell phylogenies from lineage tracing data using Cassiopeia", Genome Biology 21 (2020), 92, Methods, "Theoretical analysis of parallel evolution", Eqs. (1) and (2). <https://doi.org/10.1186/s13059-020-02000-8> PMCID: PMC7155257.
