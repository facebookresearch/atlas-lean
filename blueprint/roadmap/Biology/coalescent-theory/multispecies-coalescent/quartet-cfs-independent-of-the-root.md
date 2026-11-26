# Quartet concordance factors do not depend on the root of a network

Let $\mathcal{N}_1^+$ and $\mathcal{N}_2^+$ be metric rooted phylogenetic networks on a taxon set $X$ that
induce the same semidirected network, $\mathcal{N}_1^- = \mathcal{N}_2^-$, where the semidirected network
is obtained by deleting everything above the lowest stable ancestor, undirecting tree edges and
suppressing the resulting degree-$2$ node. Then under the network multispecies coalescent with correlated
inheritance $\mathrm{NMSC}(\rho)$, for every value of the correlation parameter $\rho \in [0,1]$ and every
$4$-taxon subset of $X$,

$$\mathrm{qCF}(\mathcal{N}_1^+) = \mathrm{qCF}(\mathcal{N}_2^+),$$

where $\mathrm{qCF}(\mathcal{N}^+) = \bigl(P_\rho(ab|cd \mid \mathcal{N}^+), P_\rho(ac|bd \mid \mathcal{N}^+), P_\rho(ad|bc \mid \mathcal{N}^+)\bigr)$
is the vector of expected quartet concordance factors. In particular the subgraph above the lowest stable
ancestor does not affect quartet concordance factors, the root of a rooted network is not identifiable
from them, and whether a $4$-taxon network is anomalous is a property of its semidirected network alone.

For $|X| > 4$ and $Y \subseteq X$ with $|Y| = 4$, the lowest stable ancestor of $Y$ may lie strictly below
that of $X$, and the quartet concordance factors for $Y$ are determined by the subgraph induced by all
paths from $\mathrm{LSA}(Y)$ to the taxa of $Y$.

## Depends on

- [Hard and soft anomalous networks under the network multispecies coalescent](anomalous-networks-under-correlated-inheritance.md)
- [Network multispecies coalescent: the gene-tree probability kernel of a fixed network](network-multispecies-coalescent-fixed-network-ge.md)

## Proof depends on

- [Network multispecies coalescent: the gene-tree probability kernel of a fixed network](network-multispecies-coalescent-fixed-network-ge.md)
- [Quartet concordance factors depend only on the unrooted quartet network](quartet-concordance-factors-depend-only-on-the-unrooted-quartet-network.md)

## Expansion

The proof is by induction on the number $n$ of hybrid nodes below the lowest stable ancestor, after
reducing to $|X| = 4$ and inserting a child edge of length $0$ below any hybrid node with two or more
children, which changes nothing in the coalescent process. The case $n = 0$ is the tree case, where the
quartet concordance factors are those of the unrooted tree and $\rho$ plays no role. For the inductive
step one conditions on the parental choices at one reticulation: the concordance factors of the network
are the mixture, with weights $\gamma_j\bigl((1-\rho)\gamma_k + \rho \mathbb{1}_{j=k}\bigr)$, of the
concordance factors of the networks obtained by fixing those choices, each of which has one fewer hybrid
node and the same semidirected network on both sides of the comparison.

## Sources

- C. Ané, J. Fogg, E. S. Allman, H. Baños and J. A. Rhodes, "Anomalous networks under the multispecies coalescent: theory and prevalence", Journal of Mathematical Biology 88 (2024), 29, <https://doi.org/10.1007/s00285-024-02050-7>. (Proposition 3.)
