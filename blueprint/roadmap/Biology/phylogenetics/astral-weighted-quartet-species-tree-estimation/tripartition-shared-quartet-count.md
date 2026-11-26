# Quartets shared by two tripartitions

Every internal node of an unrooted binary tree on a leaf set $L$ splits $L$ into three nonempty parts, a **tripartition** $A_1 \mid A_2 \mid A_3$; conversely the tripartitions determine the internal nodes. For distinct leaves $a, b, c, d$, a tripartition **induces $ab|cd$ at the pair $\{a, b\}$** if $a$ and $b$ lie in one part and $c$ and $d$ lie in the other two parts, one in each; every tree containing that node then induces the unrooted quartet tree $ab|cd$. A tripartition that induces $ab|cd$ at $\{a, b\}$ separates $c$ from $d$, so it does not induce $ab|cd$ at $\{c, d\}$. An unrooted binary tree inducing $ab|cd$ does so at exactly two of its internal nodes: one inducing it at $\{a, b\}$ and one inducing it at $\{c, d\}$.

**Formula** (Eq. 1). Let $T = A_1 \mid A_2 \mid A_3$ and $T' = B_1 \mid B_2 \mid B_3$ be tripartitions of $L$ and $C_{ij} = |A_i \cap B_j|$ for $i, j \in \{1, 2, 3\}$. The number of quartet trees that $T$ and $T'$ both induce *at the same pair* (the same two leaves grouped in one part of $T$ and in one part of $T'$) is

$$QI(T, T') = \sum_{(a, b, c) \in \mathfrak S_3} F(C_{1a}, C_{2b}, C_{3c}),$$

$$F(a, b, c) = \binom{a}{2} b c + a \binom{b}{2} c + a b \binom{c}{2} = \frac{a b c\,(a + b + c - 3)}{2},$$

where $\mathfrak S_3$ is the set of permutations of $\{1, 2, 3\}$.

For a family $\mathcal G = (g_1, \dots, g_k)$ of binary gene trees on $L$, indexed by locus so that two loci with the same topology count twice, the **tripartition weight** (Eq. 2) is

$$w(T) = \sum_{i=1}^{k} \sum_{T' \in N(g_i)} QI(T, T'),$$

where $N(g_i)$ is the set of internal nodes of $g_i$. The **weighted quartet score** of a candidate unrooted binary species tree $S$ on $L$ is the number of pairs $(i, q)$ of a locus $i$ and a four-taxon set $q$ on which $g_i$ and $S$ induce the same quartet tree; equivalently it is $k$ times the [total quartet support](../../phylogenetics/quartet-support-and-determination-of-trees-by-qu/quartet-score.md) of $S$ with $f(q, \rho)$ the fraction of the loci whose gene tree induces the resolution $\rho$ of $q$. It equals one half of the sum of $w$ over the internal nodes of $S$: a quartet tree $ab|cd$ induced by both $S$ and $g_i$ is induced at the same pair by exactly two pairs $(u, v)$ of an internal node $u$ of $S$ and an internal node $v$ of $g_i$ (the pair $\{a, b\}$ at both nodes, or the pair $\{c, d\}$ at both), and a pair of nodes inducing it at different pairs contributes nothing.

## Depends on

- [Total quartet support of a tree](../../phylogenetics/quartet-support-and-determination-of-trees-by-qu/quartet-score.md)

## Expansion

A quartet tree induced by both nodes at the same pair $\{a, b\}$ determines a matching of the parts of $T$ with the parts of $T'$, namely the one matching the part containing $a, b$ in $T$ with that in $T'$ and the parts containing $c$ and $d$ likewise; it takes $a, b$ from one matched intersection and one leaf from each of the other two. Summing over the six matchings counts each such quartet tree once. Grouping only by the unrooted topology would not do: $ab|c|d$ and $a|b|cd$ both lie on trees inducing $ab|cd$, yet every intersection of their parts has at most one element, so $QI = 0$. The closed form of $F$ follows from $\binom{a}{2} = a(a-1)/2$. ASTRAL-II accumulates the matrix $C$ in a post-order traversal of each gene tree, so $w(T)$ costs $O(nk)$ time for $n$ taxa and $k$ genes (Algorithm 1).

## Sources

- S. Mirarab, T. Warnow, *ASTRAL-II: coalescent-based species tree estimation with many hundreds of taxa and thousands of genes*, Bioinformatics (2015). <https://doi.org/10.1093/bioinformatics/btv234> (PMCID: PMC4765870)
