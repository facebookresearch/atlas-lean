# Hierarchical consistency

Let $T$ be a family of clusters (subsets of $\{1, \dots, m\}$) with levels $a_C$ and p-values $p_C$; the hierarchical procedure rejects a cluster $C \in T$ when $p_D \le a_D$ for every $D \in T$ containing $C$. If $C$ is rejected and $D \in T$ contains $C$, then $D$ is rejected.
