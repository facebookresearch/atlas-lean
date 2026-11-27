# Minimal descriptor of an ancestral recombination graph

Let $G$ be an ancestral recombination graph (ARG) on $K$ extant samples whose sequences consist of $M$ non-mixing segments (maximal segments with no internal recombination breakpoint). Then $G$ is the union of $M$ embedded marginal trees $T_1, \dots, T_M$, one per segment; each edge carries at most one strand per segment, each strand labelled by the set of mutations (SNPs) it carries, and every non-leaf vertex has several children (a **coalescent** vertex) or several parents (a **genetic-exchange** vertex). The **samples** $S(G)$ are the $K$ sequences obtained by passing the labels of strand $i$ down paths of strand $i$ to the leaves. Define:

- $G \setminus \{v\}$, removal of a non-leaf vertex $v$: in each tree $T_i$ through $v$, connect each child of $v$ in $T_i$ to the parent of $v$ in $T_i$; exactly one of these new strands is labelled by the union of the labels of the strand into $v$ and of the strand from $v$ to that child, and the others keep the labels of their old strands from $v$ (so the mutations on the strand into $v$ are not duplicated as parallel mutations); then delete $v$.
- $v$ is **resolvable** if $S(G \setminus \{v\}) \ne S(G)$, and non-resolvable otherwise.
- A coalescent vertex is **t-coalescent** if it is a coalescent node of at least one embedded tree $T_i$.
- $G'$ is **structure-preserving** for $G$ if each embedded tree of $G'$ equals the corresponding tree of $G$ in topology and branch lengths (in generations), and **samples-preserving** if $S(G') = S(G)$.
- $G$ is a **minimal descriptor** if every coalescent vertex other than the grand most recent common ancestor (GMRCA) is t-coalescent; $G_{md}$ is a minimal descriptor **of** $G$ if it is a minimal descriptor that is structure- and samples-preserving for $G$.

**Theorem.** (1) Every resolvable coalescent vertex of $G$ is t-coalescent. (2) If $U$ contains no t-coalescent vertex and $G' = G \setminus U$, then $G'$ is structure-preserving for $G$. (3) Consequently, removing from $G$ the set $U$ of all coalescent vertices other than the GMRCA that are not t-coalescent yields a minimal descriptor of $G$: it has the same marginal trees with the same branch lengths, and the same samples, hence the same allele frequencies, linkage disequilibrium and every other statistic of the sampled sequences. Vertex removals commute, $S((G\setminus\{v_1\})\setminus\{v_2\}) = S((G\setminus\{v_2\})\setminus\{v_1\})$, so the result does not depend on the order of removal; but an ARG may have several distinct minimal descriptors.

## Depends on

- [Coalescent with recombination: ancestral-material state space and generator](../coalescent-with-recombination-ancestral-material.md)

## Expansion

Removing $v$ moves the labels of the strand into $v$ onto a single one of its outgoing strands in each $T_i$, which never changes which samples receive a mutation unless $v$ has, in some $T_i$, two outgoing strands with different sets of reachable samples, so that the samples below the other strands lose those mutations; that can only happen if both strands belong to the same tree $T_i$, that is, if $v$ is a coalescent node of $T_i$. This gives (1). Topology and branch lengths of each $T_i$ are determined by its coalescent nodes, which gives (2). Removing a vertex that is not t-coalescent does not destroy the t-coalescence of the others, so after removing all of $U$ every remaining non-GMRCA coalescent vertex is t-coalescent. The construction formalises the "ancestor without ancestry" problem of random-graph ARG models: vertices whose genetic material reaches no sample, or reaches samples only along a single lineage of each tree, carry no information about the data and can be dropped without loss.

## Sources

- L. Parida, P. F. Palamara, A. Javed, "A minimal descriptor of an ancestral recombinations graph", BMC Bioinformatics 12 (Suppl. 1) (2011), S6, <https://doi.org/10.1186/1471-2105-12-s1-s6> (PMC3044314), Methods, Definitions 1–5, Observations 1–2 and Theorem 2.
