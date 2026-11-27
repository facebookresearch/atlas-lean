# Recursions for fully ranked trees with serial samples and sampled ancestors

**Definitions.** A **ranked $X$-tree** is a rooted binary phylogenetic tree on leaf labels $X$ with a linear order (ranking) of its interior nodes compatible with ancestry; for $|X| = n$ there are

$$R(n) = \frac{n!\,(n-1)!}{2^{n-1}} = \prod_{k=2}^n\binom k2$$

of them. A **fully ranked (FR) tree** also ranks the leaves: a surjection $h$ from all nodes to $\{1,\dots,l\}$, monotone along ancestry, injective on interior nodes, with leaves allowed to share a rank (a sampling time). Fix sampling epochs $1,\dots,m$ (oldest to youngest) with $n_i$ labelled individuals sampled at epoch $i$, and let $F(n_1,\dots,n_m)$ count FR trees with this pre-ranking. A **fully ranked tree with sampled ancestors (FRS)** allows a sampled individual to be a degree-two node (a direct ancestor of later samples); $S(n_1,\dots,n_m)$ counts these.

**Theorem.** $F(n) = S(n) = R(n)$ and, for $m \ge 2$,

$$F(n_1,\dots,n_m) = \sum_{i=1}^{n_m}\frac{R(n_m)}{R(i)}\,F(n_1,\dots,n_{m-2},n_{m-1}+i),$$

$$S(n_1,\dots,n_m) = \sum_{i=1}^{n_m}\sum_{j=0}^{\min(i,n_{m-1})}\binom ij\binom{n_{m-1}}{j}\frac{R(n_m)}{R(i)}\,S(n_1,\dots,n_{m-2},n_{m-1}+i-j).$$

With $A^j(\alpha) = F(n_1,\dots,n_j+\alpha)/R(\alpha)$ the first recursion becomes

$$A^j(0) = R(n_j)\sum_{i=1}^{n_j}A^{j-1}(i), \qquad A^j(\alpha+1) = \frac{(n_j+\alpha)(n_j+\alpha+1)}{\alpha(\alpha+1)}A^j(\alpha) + \frac{R(n_j+\alpha+1)}{R(\alpha+1)}A^{j-1}(n_j+\alpha+1) \quad (\alpha \ge 1),$$

(the step from $\alpha = 0$ to $\alpha = 1$ is computed directly from the first recursion), so $F(n_1,\dots,n_m)$ is computed in $O(mn)$ arithmetic steps, $n = \sum_in_i$.

## Depends on

- [Number of ranked labeled histories](../../../coalescent-theory/ranked-labeled-histories-of-coalescent-trees/card-ranked-history.md)

## Expansion

Read the tree backwards in time as a coalescent. Between the youngest epoch $m$ and epoch $m-1$, the $n_m$ youngest lineages coalesce to some number $i$ of ancestral lineages, in $R(n_m)/R(i)$ ranked ways (all ranked histories of $n_m$ lineages, divided by the ranked histories of the $i$ survivors that are not yet determined). The $i$ survivors are then treated as additional labelled samples at epoch $m-1$, which yields the recursion; distinct $i$ or distinct coalescence patterns give distinct trees. With sampled ancestors, $j$ of the $i$ ancestral lineages may coincide with individuals sampled at epoch $m-1$ (chosen in $\binom ij\binom{n_{m-1}}j$ ways), leaving $n_{m-1} + i - j$ lineages. The ratio $R(n+1)/R(n) = \binom{n+1}{2}$ is what makes the incremental update of $A^j$ cheap. Such counts normalize uniform priors on ranked tree space for serially sampled Bayesian phylogenetics.

## Sources

- A. Gavryushkina, D. Welch, A. J. Drummond, "Recursive algorithms for phylogenetic tree counting", Algorithms for Molecular Biology 8 (2013) 26, Serial sampling, Definitions 1–3, Eqs (1)–(5) and Algorithm 1, <https://doi.org/10.1186/1748-7188-8-26>, PMCID PMC3829674.
