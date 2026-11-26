# Quartets shared by two tripartitions

Every internal node of an unrooted binary tree on a leaf set $L$ splits $L$ into three nonempty parts, a **tripartition** $A_1 \mid A_2 \mid A_3$; conversely the tripartitions determine the internal nodes. A tripartition *induces* every quartet tree obtained by taking two leaves from one part and one leaf from each of the other two parts, and every tree containing that node induces these quartets.

**Formula** (Eq. 1). Let $T = A_1 \mid A_2 \mid A_3$ and $T' = B_1 \mid B_2 \mid B_3$ be tripartitions of $L$ and $C_{ij} = |A_i \cap B_j|$ for $i, j \in \{1, 2, 3\}$. The number of quartet trees induced by both is

$$QI(T, T') = \sum_{(a, b, c) \in \mathfrak S_3} F(C_{1a}, C_{2b}, C_{3c}),$$

$$F(a, b, c) = \binom{a}{2} b c + a \binom{b}{2} c + a b \binom{c}{2} = \frac{a b c\,(a + b + c - 3)}{2},$$

where $\mathfrak S_3$ is the set of permutations of $\{1, 2, 3\}$.

For a set $\mathcal G$ of gene trees, the **tripartition weight** (Eq. 2) is

$$w(T) = \sum_{g \in \mathcal G} \sum_{T' \in N(g)} QI(T, T'),$$

where $N(g)$ is the set of internal nodes of $g$. The **weighted quartet score** of a candidate species tree, the number of quartet trees in the multiset induced by $\mathcal G$ that it also induces, equals one half of the sum of $w$ over its internal nodes, because each induced quartet is counted at exactly two nodes.

## Depends on

- [Total quartet support of a tree](../../phylogenetics/quartet-support-and-determination-of-trees-by-qu/quartet-score.md)

## Expansion

A quartet induced by both nodes uses, for one matching of the parts of $T$ with the parts of $T'$, two leaves from one matched intersection and one leaf from each of the other two; summing over the six matchings counts each shared quartet once. The closed form of $F$ follows from $\binom{a}{2} = a(a-1)/2$. ASTRAL-II accumulates the matrix $C$ in a post-order traversal of each gene tree, so $w(T)$ costs $O(nk)$ time for $n$ taxa and $k$ genes (Algorithm 1).

## Sources

- S. Mirarab, T. Warnow, *ASTRAL-II: coalescent-based species tree estimation with many hundreds of taxa and thousands of genes*, Bioinformatics (2015). <https://doi.org/10.1093/bioinformatics/btv234> (PMCID: PMC4765870)
