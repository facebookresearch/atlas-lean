# Roots are tested unconditionally

Let $T$ be a family of clusters (subsets of $\{1, \dots, m\}$) with levels $a_C$ and p-values $p_C$; the hierarchical procedure rejects a cluster $C \in T$ when $p_D \le a_D$ for every $D \in T$ containing $C$. If no member of $T$ strictly contains $C$, then $C$ is rejected if and only if $C \in T$ and $p_C \le a_C$.
