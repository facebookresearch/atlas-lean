# Siblings are tested together

Let $T$ be a family of clusters with p-values $p_C$ and a level $q$. The sibling family of $C$ is the set of members of $T$ with the same strict ancestors as $C$; Yekutieli's procedure tests each node at the Benjamini–Hochberg cutoff $qk_S/|S|$ of its family $S$ ($k_S$ the BH index of the family's p-values) and rejects a node when it and all its ancestors in $T$ pass their levels; a family is tested when every strict ancestor passed its level. If $D$ is a sibling of $C$, then $D$ is tested if and only if $C$ is tested.
