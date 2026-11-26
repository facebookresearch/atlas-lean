# Tree false discovery rate control of Yekutieli’s procedure

Let $T$ be a family of clusters with p-values $p_C$ and a level $q$. The sibling family of $C$ is the set of members of $T$ with the same strict ancestors as $C$; Yekutieli's procedure tests each node at the Benjamini–Hochberg cutoff $qk_S/|S|$ of its family $S$ ($k_S$ the BH index of the family's p-values) and rejects a node when it and all its ancestors in $T$ pass their levels; a family is tested when every strict ancestor passed its level. Suppose the p-values of the nodes of $T$ are measurable on a probability space and the true-null ones ($H_0$) valid. Suppose that within each sibling family the p-values are mutually independent and independent of the p-values outside the family, and let $q \in [0, 1]$. Then the tree false discovery rate is at most $q\sum_S\frac{|S \cap H_0|}{|S|}P(S\text{ is tested})$, summed over the families of $T$.

## Sources

- Yekutieli (2008).
