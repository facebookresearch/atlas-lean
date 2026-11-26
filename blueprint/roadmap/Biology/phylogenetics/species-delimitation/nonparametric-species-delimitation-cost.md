# Nonparametric species delimitation cost

Let $G_1, \dots, G_g$ be rooted binary gene trees on (subsets of) a sample set, and let $\mathcal{D}$ be a delimited species tree with species $1, \dots, s$. The **nonparametric delimitation cost** combines two non-negative components.

**Gene-tree conflict.** $C_{\mathrm{conf}}(\mathcal{D}) = \sum_{\ell = 1}^{g} \mathrm{dup}(G_\ell, \mathcal{D})$, where $\mathrm{dup}$ is the minimum number of gene duplications needed to reconcile $G_\ell$ with the species tree of $\mathcal{D}$ (the gene-tree parsimony criterion), counting only lineage-sorting events on interspecific branches. It measures oversplitting or a wrong species topology.

**Excess structure.** Within each species $a$, decompose every gene tree into its maximal subtrees whose samples all belong to $a$, and for each pair of loci $\ell < \ell'$ let $\pi_{a,\ell\ell'}$ be the probability, under the neutral coalescent in a single panmictic population with the same sample size, of at least as many shared rooted triplets as observed between the two gene trees. Then

$$C_{\mathrm{str}}(\mathcal{D}) = \frac{1}{g} \sum_{a = 1}^{s} \sum_{\ell < \ell'} \left(\frac{1}{\pi_{a,\ell\ell'}} - 1\right).$$

It measures undersplitting: a species hiding several lineages produces more triplet agreement between loci than panmixia allows.

The **total cost** is a weighted sum of $C_{\mathrm{conf}}$ and $C_{\mathrm{str}}$ with a user-chosen relative weight on structure (default $0.5$), minimized over delimited species trees by heuristic search; an optional $P$-threshold counts only structure terms with $\pi$ below a cutoff.

Properties:

- both components are $0$ in the ideal case: no conflict on interspecific branches and no more triplet sharing than expected within species ($1/\pi - 1 = 0$ when $\pi = 1$);
- conflict grows linearly in the number of loci and the pairwise structure sum quadratically, so dividing the latter by $g$ puts both on the same scale;
- a weight too low on structure favours lumping (conflicts move inside species and stop being counted), a weight too high favours splitting.

## Depends on

- [Number of delimited species trees](number-of-delimited-species-trees.md)

## Expansion

Under neutral coalescence without structure each gene tree is an independent random draw, so triplet overlap between loci within a species should look like that of independent coalescent trees; the null distribution was tabulated by simulation for up to 50 samples per species (with an analytic approximation beyond), and $\pi$ is its upper tail. Taking reciprocals converts small tail probabilities (strong structure) into large costs, and subtracting $1$ makes the minimum zero. The conflict component is the classical duplication cost computed by a fast reconciliation algorithm; the minimum number of deep coalescences is the alternative that also charges each branch over which duplicate lineages persist.

## Sources

- B. C. O'Meara, "New heuristic methods for joint species delimitation and species tree inference", Systematic Biology 59 (2010), 59–73, section "Approach 2: nonparametric delimitation", <https://doi.org/10.1093/sysbio/syp077> (PMC5841455).
