# A cluster is tested only if its parent is rejected

Let $T$ be a family of clusters (subsets of $\{1, \dots, m\}$) with levels $a_C$ and p-values $p_C$; the hierarchical procedure rejects a cluster $C \in T$ when $p_D \le a_D$ for every $D \in T$ containing $C$. If $D$ is the parent of $C$, then $C$ is rejected if and only if $p_C \le a_C$ and $D$ is rejected.
