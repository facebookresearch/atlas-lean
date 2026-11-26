# Direct and indirect connectivity statistics of associated loci

Let $G$ be a reference interaction graph and $\mathcal{L}_1, \dots, \mathcal{L}_m$ the protein sets of $m$ associated loci, with $\mathcal{A} = \bigcup_k \mathcal{L}_k$ the associated proteins. Define:

- the **direct network**, the subgraph of $G$ induced on $\mathcal{A}$ with edges between proteins of *different* loci;
- the **indirect network**, obtained by adding every protein $w \notin \mathcal{A}$ adjacent to at least two proteins of different loci; such a $w$ is a **common interactor**.

Four statistics summarize them. The edge statistic is

$$T_{\text{direct}} = \#\big\{ \{u, v\} \in E(G) : u \in \mathcal{L}_j,\, v \in \mathcal{L}_k,\, j \ne k \big\}.$$

The node statistics are, for a protein $u \in \mathcal{L}_j$, its **direct connectivity** $\#\{k \ne j : u \text{ is adjacent to some } v \in \mathcal{L}_k\}$ and its **indirect connectivity**, the same count allowing paths of length two through a common interactor; and for a common interactor $w$, the number of distinct loci it binds, averaged over common interactors.

Each statistic is tested against the [within-degree node-label permutation null](within-degree-node-label-permutation.md). The edge statistic and the node statistics answer different questions, and the pair separates two shapes of network: a path $a - b - c - d - e$ through five loci has a significant edge count but unremarkable node statistics, while a tightly clustered network in which a few proteins each touch many loci has significant node statistics as well.

**Gene prioritization.** Within a multi-gene locus the proteins compete: each is scored by how much of the network's excess connectivity it accounts for, by an iterative scheme that re-scores a protein against the networks built from the other loci's current best candidates, and the highest-scoring protein of each locus is nominated as the candidate gene. The nomination uses network participation only; that the nominated genes turn out to lie nearest the lead variant more often than chance ($p \approx 0.005$) is a check on the procedure, not an input to it.

## Depends on

- [Within-degree node-label permutation null for interaction networks](within-degree-node-label-permutation.md)

## Expansion

Restricting edges to pairs from different loci is what prevents the statistics from rewarding physical proximity on the chromosome: proteins encoded close together are often paralogues or members of one complex, and counting their interactions would turn gene clustering into apparent biological connectivity. The indirect network exists because the relation "shares a process with" is not the relation "binds": two risk proteins acting in one pathway may each bind a third. Common interactors are then natural candidates to carry undiscovered risk variation, and testing their association scores against the genome-wide distribution of gene-containing regions is a prediction the design can check — in the two immune diseases analyzed, common interactors expressed in the same tissues as the associated proteins were enriched for association signal beyond chance. The method is blind to proteins absent from the reference graph, so a negative result for a locus is uninformative about it.

## Sources

- E. J. Rossin, K. Lage, S. Raychaudhuri et al., "Proteins encoded in genomic regions associated with immune-mediated disease physically interact and suggest underlying biology", PLoS Genetics 7 (2011), e1001273, Results ("A method to assess network connectivity", "Candidate gene nomination") and Text S1, <https://doi.org/10.1371/journal.pgen.1001273>, PMCID PMC3020935.
