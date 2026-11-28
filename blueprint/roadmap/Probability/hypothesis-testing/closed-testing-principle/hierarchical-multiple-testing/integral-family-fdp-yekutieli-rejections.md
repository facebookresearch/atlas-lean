# Per-family false discovery rate control of Yekutieli’s procedure

Let $T$ be a family of clusters with p-values $p_C$ and a level $q$. The sibling family of $C$ is the set of members of $T$ with the same strict ancestors as $C$; Yekutieli's procedure tests each node at the Benjamini–Hochberg cutoff $qk_S/|S|$ of its family $S$ ($k_S$ the BH index of the family's p-values) and rejects a node when it and all its ancestors in $T$ pass their levels; a family is tested when every strict ancestor passed its level. Suppose the p-values of the nodes of $T$ are measurable on a probability space, and let $q \in [0, 1]$. Let $S$ be the family of $C$, whose true-null p-values (those of $S \cap H_0$) are valid, whose p-values are mutually independent, and whose p-value vector is independent of the p-values of the nodes outside $S$. Then the expected family false discovery proportion in $S$ is at most $q\frac{|S \cap H_0|}{|S|}P(S\text{ is tested})$.

## Sources

- Yekutieli (2008), the per-family step of the FDR analysis; the within-family bound is Benjamini & Hochberg (1995), Theorem 1.
