# Concordance-factor detectability of 4-blobs on 4-taxon networks

Let $\mathcal{N}^+$ be a 4-taxon rooted binary phylogenetic network on $\{a, b, c, d\}$ under
the network multispecies coalescent (NMSC), with theoretical quartet concordance factor
$\mathrm{CF}_{abcd} = (p_{ab|cd}, p_{ac|bd}, p_{ad|bc}) \in \Delta_2$ giving the
probabilities of the three unrooted gene-tree quartet topologies. Call $\mathrm{CF}_{abcd}$
**strictly $(ab|cd)$-cut** if $p_{ac|bd} = p_{ad|bc}$ and $p_{ab|cd} \ne p_{ac|bd}$, and
**non-cut** if no two of its coordinates are equal.

Then for generic numerical parameters (outside a set of measure zero in edge-length and
hybridization-parameter space) on $\mathcal{N}^+$:
1. $T_{\mathrm{rd}}(\mathcal{N}^-)$ has resolved quartet topology $ab|cd$ if and only if $\mathrm{CF}_{abcd}$ is strictly $(ab|cd)$-cut.
2. $T_{\mathrm{rd}}(\mathcal{N}^-)$ is unresolved (a 4-blob) if and only if $\mathrm{CF}_{abcd}$ is non-cut.

## Depends on

- [Blobs and the reduced unrooted tree of blobs of a phylogenetic network](blob-and-tree-of-blobs-of-a-phylogenetic-network.md)

## Expansion

If $T_{\mathrm{rd}}(\mathcal{N}^-)$ has topology $ab|cd$, then $\mathcal{N}^+$ has a cut edge
separating $\{a, b\}$ from $\{c, d\}$; by exchangeability of coalescent lineages that fail to
coalesce below that cut edge, $p_{ac|bd} = p_{ad|bc}$, and the analytic function
$p_{ab|cd} - p_{ac|bd}$ is not identically zero. Conversely, if $T_{\mathrm{rd}}(\mathcal{N}^-)$
is unresolved, a minimal 4-blob reduction shows that the three pairwise differences among coordinates
of $\mathrm{CF}_{abcd}$ are non-zero analytic functions of the numerical parameters, hence
non-vanishing generically.

## Sources

- E. S. Allman, H. Baños, J. D. Mitchell, and J. A. Rhodes, "The tree of blobs of a species network: identifiability under the coalescent", Journal of Mathematical Biology 86 (2023), 10 (published online 2022), <https://doi.org/10.1007/s00285-022-01838-9> (PMC10062380). (Theorem 1.)
