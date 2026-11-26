# Extra-lineage formula and non-heredity of minimum deep coalescence trees

**Setting.** Let $T$ (gene tree) and $S$ (species tree) be rooted binary phylogenetic trees on the same taxon set $X$. Embed $T$ in $S$ by sending each leaf to its counterpart and each internal node $v$ of $T$ onto the edge above the most recent common ancestor in $S$ of its cluster $C_T(v)$. The **number of extra lineages** on an edge of $S$ is the number of gene lineages leaving that edge toward the root, minus one; their sum over edges is the **MDC score** $l(T,S)$ (it is not symmetric in $T$ and $S$).

**Theorem (extra-lineage formula).** For an edge $(u', v')$ of $S$ with cluster $C_S(v')$ below it, let $t_1, \dots, t_k$ be the maximal clades of $T$ whose leaf sets are contained in $C_S(v')$. Then the number of extra lineages on $(u', v')$ is $k - 1$, and $l(T,S) = \sum_{(u',v')}(k_{(u',v')} - 1)$.

**Definition.** A species tree $S$ is a **minimum deep coalescence (MDC) tree** for a multiset $G_m = \{T_1, \dots, T_m\}$ of gene trees if

$$S \in \operatorname*{arg\,min}_{S'} \sum_{i=1}^m l(T_i, S') = \operatorname*{arg\,min}_{S'} \sum_{T \in G} x_T\, l(T, S'),$$

where $x_T$ is the multiplicity of $T$ in $G_m$. An MDC tree $S$ is **hereditary** if for some taxon $i$ the restriction $S|_{X\setminus\{i\}}$ is an MDC tree for the restricted gene trees $\{T|_{X\setminus\{i\}} : T \in G_m\}$.

**Theorem (non-heredity).** There exist gene-tree multisets whose MDC tree $S$ is unique but such that $S|_Y$ is not an MDC tree for the restricted gene trees for any $Y \subset X$ with $|Y| = |X| - 1$. Already for $|X| = 4$ (where every such $Y$ is a triple), explicit multisets exhibit this for both the caterpillar and the balanced tree shape, both when the unique MDC tree does not occur among the gene trees at all (for instance a multiset of 29 gene trees for the caterpillar case) and when it is the most frequent gene tree. Hence deleting a single taxon can change the inferred species-tree topology on the remaining taxa.

## Expansion

In the embedding, each edge of $S$ carries the lineages of $T$ whose subtrees fit entirely below it; these are exactly the maximal clades with leaf set inside $C_S(v')$, and only one lineage per species-tree lineage is "free", giving $k - 1$. Summing gives $l(T,S)$ cheaply, so for four taxa the full $15 \times 15$ table of scores $l(T_i, T_j)$ can be tabulated, and finding a non-hereditary instance reduces to a system of linear inequalities in the multiplicities $x_T$: the chosen tree must beat the 14 others on four taxa, while on each of the four triples some other rooted triple must beat its restriction. Integer solutions of such systems give the counterexamples, by the same technique used to prove non-heredity of maximum parsimony. Non-heredity is undesirable for a species-tree estimator, since including or excluding one taxon should not alter the inferred relationships of the others.

## Sources

- Mareike Fischer, Martin Kreidl, "Non-hereditary Minimum Deep Coalescence trees", arXiv (2015). Theorem 1 (citing Than and Nakhleh), Definitions 1–2, Observation 1, Examples 1–4. <https://doi.org/10.48550/arXiv.1507.07209>
