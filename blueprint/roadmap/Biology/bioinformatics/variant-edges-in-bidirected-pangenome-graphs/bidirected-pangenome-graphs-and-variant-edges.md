# Bidirected pangenome graphs and variant edges

**Bidirected graph.** A bidirected graph $B = (V, E, C)$ is a directed graph $(V, E)$ with a fixed-point-free involution $C : V \to V$, $v \mapsto v^c$ ($(v^c)^c = v$, $v \ne v^c$), such that for every edge $e = (u, v) \in E$ its complement $e^c = (v^c, u^c)$ is also in $E$. The node pairs $\{v, v^c\}$ are *binodes* (a DNA segment read on either strand) and the edge pairs $\{e, e^c\}$ are *biedges*. A *walk* between binodes $\{v_1, v_1^c\}$ and $\{v_n, v_n^c\}$ is a pair of node sequences $(v_1, \dots, v_n)$ and $(v_n^c, \dots, v_1^c)$ with $(v_i, v_{i+1}) \in E$; it is a *path* if no binode repeats. A haplotype is a collection of walks.

**Reference tree.** $B$ is a *rooted tree* with root $\{r, r^c\}$ if, for one orientation $r$ of the root, every binode has exactly one of its nodes reachable from $r$ by a unique directed path. A rooted tree is *oriented*: $V$ splits into $V^+$ and $V^-$ with no edges between them and $v \in V^+ \iff v^c \in V^-$. A *reference tree* $T$ of $B$ is a rooted spanning tree (a spanning subgraph closed under complement that is a rooted tree). It induces two directed *half-trees*, $T^+$ on $V^+$ and $T^- = (T^+)^c$ on $V^-$.

**Variant edges and genotypes.** The *variant edges* of $B$ with respect to $T$ are the biedges not in $T$. A variant biedge joining $V^+$ to $V^-$ (in either direction) is an *inversion edge*; otherwise it has a representative of the form $(u^+, v^+)$. The *genotype* of a walk $W$ is the vector $x(W) = (x_e(W))_e$ of the number of times $W$ traverses each variant biedge $e$, and the genotype of an individual is the sum over its walks.

**Visit-count lemma.** Let $W$ be a walk from $v_0$ to $u_0$ that traverses the variant edges $(u_1, v_1), \dots, (u_n, v_n)$ in order. For $i = 0, \dots, n$ call $v_i$ a *source* if $v_i \in V^+$, and otherwise call $v_i^c$ a *sink*; call $u_i$ a *sink* if $u_i \in V^+$, and otherwise call $u_i^c$ a *source*. For $v \in V^+$ let $D(v) \subseteq V^+$ be the set of nodes reachable from $v$ in $T^+$. Then $W$ visits the binode $\{v, v^c\}$ exactly

$$\big|D(v) \cap \mathrm{sinks}(W)\big| - \big|(D(v) \setminus \{v\}) \cap \mathrm{sources}(W)\big|$$

times, counting sources and sinks with multiplicity.

## Proof sketch

Between consecutive variant edges a walk moves only along tree edges, and in $T^+$ (or its complement) the move is the unique directed path from a source to a sink. Decompose $W$ into such tree paths $S_0, \dots, S_n$, each running inside $V^+$ from the $i$-th source to the $i$-th sink (using $W^c$ where $W$ runs through $V^-$). A directed tree path cannot leave the subtree $D(v)$ once inside it and can enter it only through $v$; so a path that avoids $v$ starts and ends on the same side of $D(v)$, and a path from outside $D(v)$ to inside it passes through $v$. A tree path visits $v$ if and only if it ends in $D(v)$ and starts at $v$ or outside $D(v)$ (strictly above $v$); subtracting sources in $D(v) \setminus \{v\}$ rather than all of $D(v)$ accounts for paths that start at $v$ itself (the printed statement of Lemma 2 in the source omits the multiplicity of $v$ among the sources, which instead counts traversals of the tree biedge entering $\{v, v^c\}$ from its parent). Bidirected graphs encode the two strands of DNA: reading a binode in one direction gives the forward sequence and in the other its reverse complement.

## Sources

- P. Salehi Nowbandegani, S. Zhang, H. Hu, H. Li, L. J. O'Connor, "Defining and cataloging variants in pangenome graphs", Cell Genomics (2026), <https://doi.org/10.1016/j.xgen.2026.101327> (PMC13576716).
