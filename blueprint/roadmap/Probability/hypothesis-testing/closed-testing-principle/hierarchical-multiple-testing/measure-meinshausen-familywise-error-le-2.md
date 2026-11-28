# Meinshausen’s hierarchical procedure controls the familywise error rate

Let $T$ be a family of clusters (subsets of $\{1, \dots, m\}$) with levels $a_C$ and p-values $p_C$; the hierarchical procedure rejects a cluster $C \in T$ when $p_D \le a_D$ for every $D \in T$ containing $C$. Let $T$ be laminar, $H_0 \subseteq T$ the true-null clusters with valid p-values, and use the levels $\alpha|C|/m$ with $\alpha \in [0, 1]$. Then the probability of rejecting some true-null cluster is at most $\alpha$, under arbitrary dependence.

## Sources

- Meinshausen (2008), Theorem 1.
