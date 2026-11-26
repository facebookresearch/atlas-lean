# Viable genotype space of an epistatic network and dense-community variant detection

**Model.** Let $L$ biallelic loci carry genotypes in the hypercube $\{0,1\}^L$. The *epistatic network* $G$ has the loci as vertices, with $u\sim v$ iff the double mutant $(1,1)$ at $u,v$ is viable, i.e. the pair is not under the negative epistasis $f_{11}<f_{10}+f_{01}-f_{00}$ that drives fitness to $f_{11}\le0$. A genotype is viable iff its set of alternative alleles is a clique of $G$.

**Proposition.** The viable space is the union, over the inclusion-maximal cliques $C$ of $G$, of the sub-hypercubes $H(C)=\{g\in\{0,1\}^L:\ g_i=0\ \text{for } i\notin C\}$. Within each $H(C)$ only additive or positive epistatic effects occur. Evolutionary trajectories confined to $H(C)$ therefore accumulate the alternative alleles of $C$ and converge to the genotype $g_C$ carrying all of them, so every trajectory in the viable space ends at a genotype determined by a maximal clique of $G$.

**Density-based significance of a haplotype.** Approximate $G$ by an inferred coordinated substitution network $G_t$, and view a haplotype as a vertex set $H\subseteq V(G_t)$ with density

$$d_{G_t}(H)=\frac{|E(G_t[H])|}{|H|}.$$

Given a sample $S^*$ of *connected* induced subgraphs of size $|H|$, the density P value is

$$p_{G_t}(H)=\frac{\bigl|\{S_j\in S^*:\ d_{G_t}(S_j)\ge d_{G_t}(H)\}\bigr|}{|S^*|}.$$

If $G_t[H]$ is disconnected, $H$ is replaced by its largest connected component. Emerging variants are predicted as dense communities of $G_t$.

## Depends on

- [Linkage bound for a non-viable double mutant under the quasispecies model](linkage-bound-for-a-non-viable-double-mutant-under-the-quasispecies-model.md)

## Expansion

A genotype with alternative alleles at $A$ is viable iff no pair in $A$ is negatively epistatic, i.e. iff $A$ is a clique, so the viable set is the downward-closed family of cliques, which is covered by the maximal cliques. Because inferred networks miss true links, the method looks for dense subgraphs rather than exact cliques. Sampling must be restricted to connected subgraphs: sparse networks make random vertex sets mostly disconnected, which would give spuriously small P values to any connected haplotype. For example, a tree on $10$ vertices is the least dense connected subgraph and has connected-sampling P value $1$, while naive sampling assigned it about $1.9\times10^{-4}$. Connected $k$-subgraphs are drawn by randomized backtracking enumeration with an exclusion set, following the network-motif sampling scheme.

## Sources

- F. Mohebbi, A. Zelikovsky, S. Mangul, G. Chowell, P. Skums, "Early detection of emerging viral variants through analysis of community structure of coordinated substitution networks", *Nature Communications* 15:2838 (2024), Methods, "Model-based rationale of the proposed approach" (Fig. 5) and "Estimation of density-based P values of viral haplotypes", Eqs. (13)–(14), Algorithm 1, <https://doi.org/10.1038/s41467-024-47304-6>, PMCID PMC10987511.
