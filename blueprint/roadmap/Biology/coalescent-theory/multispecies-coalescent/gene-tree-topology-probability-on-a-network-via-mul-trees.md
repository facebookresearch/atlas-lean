# Gene tree topology probabilities on a phylogenetic network via MUL-trees and allele mappings

Let $\Psi$ be a rooted binary species network on species set $\mathcal{X}$ with branch lengths in coalescent units and an inheritance probability on each reticulation edge, with gene lineages evolving under [the network multispecies coalescent](network-multispecies-coalescent-fixed-network-ge.md). For a locus, let $A_x$ be the set of alleles sampled from species $x$ and $G$ a rooted gene tree topology on $\bigcup_x A_x$.

**Construction.**

1. *(MUL-tree.)* Traverse $\Psi$ from the leaves toward the root. At each reticulation $v$, delete its two incoming edges, make two copies of the subtree below $v$ and attach one copy to each former parent of $v$. The result is a multilabelled tree $T$ whose leaves labelled $x$ form a set $L_x$, together with a map $f$ sending each branch of $T$ to the branch of $\Psi$ it copies; branch lengths and inheritance probabilities are transferred along $f$.
2. *(Allele mappings.)* A valid allele mapping is a function $m$ sending every allele in $A_x$ to some leaf in $L_x$, for every $x$; let $\mathcal{M}$ be the set of valid mappings.
3. *(Summation.)* Then

$$P(G \mid \Psi) = \sum_{m \in \mathcal{M}} P(G \mid T, m),$$

where $P(G \mid T, m)$ is computed by summing over coalescent histories on $T$, with two corrections: each branch carries the inheritance probability of the network branch it copies (raised to the number of lineages routed through it), and the branches of $T$ in a common preimage $f^{-1}(b)$ are treated jointly, so that the number of lineages entering (and leaving) network branch $b$ is the sum over its copies, and the coalescent factor for $b$ is the probability that this total number of lineages coalesces to the total exiting number within the length of $b$, with Degnan–Salter ordering counts for the coalescences.

Given independent loci with gene trees $G_1, \dots, G_m$, the likelihood of $\Psi$ is $\prod_i P(G_i \mid \Psi)$. With one reticulation and three species, a network that mixes two species-tree resolutions can match any observed vector of the three rooted gene tree frequencies in which the minimum frequency lies strictly between $0$ and $1/3$ and is strictly below the other two frequencies. A zero frequency cannot be matched, because the least frequent topology has probability $\tfrac13 e^{-t} > 0$ for every finite branch length $t$; the source gives "the unique solution t = −log(3p3), γ = (p2 − p3)/(1 − 3p3) for p3 < 1/3 and 0 < p3 < p2, p1" (Equation 9).

## Depends on

- [Network multispecies coalescent: the gene-tree probability kernel of a fixed network](network-multispecies-coalescent-fixed-network-ge.md)
- [The multispecies coalescent](gene-tree-prob.md)

## Expansion

Each allele mapping fixes, for every lineage, the sequence of parental edges it takes at reticulations, so summing over mappings sums over all routings of lineages through the network, as the network coalescent requires. Lineages routed into different copies of the same network branch nonetheless share one population, so treating the copies separately would forbid coalescences between them; pooling their lineage counts along $f^{-1}(b)$ restores the correct within-branch coalescent law. When $\Psi$ is a tree, $T = \Psi$, $\mathcal{M}$ has one element, and the formula reduces to the Degnan–Salter sum over coalescent histories. The number of mappings grows exponentially in the number of reticulations and sampled alleles, which limits direct use to small networks. For the three-taxon statement, if both parental resolutions share internal branch length $t$ and the hybrid taxon follows the second resolution with probability $\gamma$, the gene tree probabilities are mixtures of the tree probabilities $1 - \tfrac23 e^{-t}$ and $\tfrac13 e^{-t}$; the least frequent topology fixes $e^{-t} = 3p_{\min}$ and the other two fix $\gamma$.

## Sources

- Y. Yu, J. H. Degnan and L. Nakhleh, "The Probability of a Gene Tree Topology within a Phylogenetic Network with Applications to Hybridization Detection", PLoS Genetics 8 (2012), e1002660, Results, "The probability of a gene tree topology within a species network" (Steps 1–3, Equations 3–6) and the three-taxon analysis (Equation 9), <https://doi.org/10.1371/journal.pgen.1002660> (PMC3330115).
- J. H. Degnan and L. A. Salter, "Gene tree distributions under the coalescent process", Evolution 59 (2005), 24–37, <https://doi.org/10.1111/j.0014-3820.2005.tb00891.x>.
