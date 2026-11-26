# Per-family false discovery rate for independent node p-values

On a probability space, let $T$ be a family of clusters with p-values $p_C$ and a level $q$. The sibling family of $C$ is the set of members of $T$ with the same strict ancestors as $C$; Yekutieli's procedure tests each node at the Benjamini–Hochberg cutoff $qk_S/|S|$ of its family $S$ ($k_S$ the BH index of the family's p-values) and rejects a node when it and all its ancestors in $T$ pass their levels; a family is tested when every strict ancestor passed its level. If the p-values of the nodes of $T$ are measurable and mutually independent with valid true-null p-values and $q \in [0, 1]$, then the expected family false discovery proportion in the family $S$ of $C$ is at most $q\frac{|S \cap H_0|}{|S|}P(S\text{ is tested})$.

## Sources

- Yekutieli (2008).
