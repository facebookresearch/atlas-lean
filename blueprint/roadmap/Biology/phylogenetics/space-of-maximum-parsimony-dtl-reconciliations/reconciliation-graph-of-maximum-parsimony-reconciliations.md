# Reconciliation graph of maximum parsimony DTL reconciliations

A **DTL instance** $(S, G, \phi, d, t, \ell)$ consists of rooted binary trees $S = (V_S, E_S)$ (species or host) and $G = (V_G, E_G)$ (gene or parasite), a leaf map $\phi$ from leaves of $G$ to leaves of $S$, and nonnegative duplication, transfer and loss costs. A **reconciliation** is a map $\Phi: V_G \to V_S$ with $\Phi(g) = \phi(g)$ on leaves such that, for an internal $g$ with children $g', g''$, $\Phi(g)$ is not a descendant of $\Phi(g')$ or $\Phi(g'')$ and at least one of $\Phi(g'), \Phi(g'')$ is equal to or below $\Phi(g)$. Each internal $g$ induces one **speciation** (children mapped into different child subtrees of $\Phi(g)$), **duplication** (both at or below $\Phi(g)$, not a speciation) or **transfer** (exactly one at or below $\Phi(g)$, the other incomparable), and each species vertex strictly crossed by the image of a gene edge induces a **loss**. A **maximum parsimony reconciliation** (MPR) minimizes $d\,\#\mathrm{dup} + t\,\#\mathrm{transfer} + \ell\,\#\mathrm{loss}$; one is found in $O(|G||S|)$ time, but their number can be exponential in the tree sizes.

The **reconciliation graph** $\mathcal R$ has a **mapping node** $(g, s)$ for each gene vertex $g$ mapped to, or passing through, species vertex $s$ in some MPR, and an **event node** for each speciation, duplication, transfer, loss or leaf association $(g, s)$ used by some MPR, with arcs from $(g, s)$ to its event nodes and from each event node to the mapping nodes of its child associations. A **traversal** is a subgraph rooted at a source $(r_G, \cdot)$ that takes exactly one event child at each non-leaf mapping node and all mapping children of each chosen event node.

**Facts.** With $n = |V_S|$ and $m = |V_G|$:

- (bijection) MPRs correspond bijectively to traversals of $\mathcal R$, so an MPR $R$ can be identified with its event set $E(R)$;
- (Lemma 1 of the clustering paper) $\mathcal R$ has $O(n^2 m)$ nodes and $O(n^2 m)$ arcs, and for undated trees it is acyclic and constructible in $O(m n^2)$ time;
- (Lemma 1 of the pairwise-distance paper) if $t, \ell > 0$, every MPR has $O(m)$ events, so the symmetric distance $|E(R_1) \oplus E(R_2)|$ between MPRs is $O(m)$.

## Expansion

There are $O(nm)$ mapping nodes. Each has $O(n)$ event children: two ways to realize a speciation, one duplication, up to two losses and $O(n)$ transfers (one child stays, the other moves to one of $n$ vertices); event nodes have at most two children, giving the $O(n^2 m)$ bound. For the event bound, mapping the gene root to any species leaf and embedding everything else by transfers gives a valid reconciliation of cost $tm$, so an MPR has total cost at most $tm$, hence at most $tm/\ell$ losses, plus one non-loss event per internal gene vertex. Because shared mappings and events are stored once, quantities over the exponentially many MPRs (counts, event frequencies, distance distributions, medians) become dynamic programs over $\mathcal R$.

## Sources

- R. Mawhorter, R. Libeskind-Hadas, "Hierarchical clustering of maximum parsimony reconciliations", BMC Bioinformatics 20:612 (2019), Background (reconciliation graphs and traversals) and Lemma 1, <https://doi.org/10.1186/s12859-019-3223-5>, PMCID PMC6882150.
- S. Santichaivekin, R. Mawhorter, R. Libeskind-Hadas, "An efficient exact algorithm for computing all pairwise distances between reconciliations in the duplication-transfer-loss model", BMC Bioinformatics 20(Suppl 20):636 (2019), Background and Lemma 1, <https://doi.org/10.1186/s12859-019-3203-9>, PMCID PMC6915856.