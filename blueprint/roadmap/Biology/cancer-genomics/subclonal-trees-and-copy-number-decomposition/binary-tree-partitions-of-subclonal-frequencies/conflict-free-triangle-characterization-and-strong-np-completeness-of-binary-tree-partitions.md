# Conflict-free triangle characterization and strong NP-completeness of binary tree partitions

**Model.** A tumour sample is a population of cells descended from one founder by successive clonal expansions. Assume (i) infinite sites: each locus mutates at most once in the history of the tumour, and (ii) at most one cell starts a clonal expansion at any time. Each expansion splits the current population into the cells carrying the new mutation and the rest, so the history is a rooted binary tree whose node $v$ carries the frequency $a_v \in (0,1]$ of cells with the mutations on the edge above $v$, and every internal node satisfies the **children-sum-to-parent (CSP) condition**

$$a_v = \sum_{u \text{ child of } v} a_u .$$

**Definitions.** Let $L = \{a_1, \dots, a_n\}$ be a multiset with $0 < a_i \le 1$.

- A **binary tree partition (BTP)** of $L$ is a complete rooted binary tree (every node has $0$ or $2$ children) with nodes $v_1, \dots, v_n$, node $v_i$ of weight $a_i$, in which every internal node satisfies CSP. The **BTP problem** asks whether $L$ has a BTP.
- A **triangle** of $L$ is a pair $(k, \{i, j\})$ of distinct indices with $a_i + a_j = a_k$; $k$ is its peak and $i, j$ its tails. Two triangles are **in conflict** if they have the same peak or share a tail. A set of triangles is **conflict-free** if no two of its triangles conflict.

**Theorem (characterization).** Let $|L| = 2q - 1$. Then $L$ has a BTP if and only if $L$ contains $q - 1$ pairwise conflict-free triangles. Moreover, every conflict-free set of triangles of $L$ has at most $q - 1$ elements, and $|L|$ odd is necessary for a BTP to exist.

**Theorem (complexity).** The BTP problem is NP-complete in the strong sense, that is, it remains NP-complete when the entries of $L$ are integers bounded by a polynomial in $n$ (after rescaling). The analogous problem for non-binary trees is NP-complete by a reduction from subset sum.

The hardness proof reduces from **numerical matching with target sums**: given positive integers $X = \{x_1,\dots,x_m\}$, $Y = \{y_1,\dots,y_m\}$, $B = \{b_1,\dots,b_m\}$, decide whether there are permutations $\pi_X, \pi_Y$ with $x_{\pi_X(i)} + y_{\pi_Y(i)} = b_i$ for all $i$. Set

$$\hat x_i = 4(m+1)x_i + 1,\quad \hat y_i = 4(m+1)y_i + 3,\quad \hat b_i = 4(m+1)b_i + 4,\quad \beta_j = \sum_{k=1}^{j} \hat b_k \ (2 \le j \le m),$$

and $L_I = \{\hat x_i\} \cup \{\hat y_i\} \cup \{\hat b_i\} \cup \{\beta_2, \dots, \beta_m\}$, a multiset of $4m - 1$ elements. The instance is solvable if and only if $L_I$ has a BTP, and solutions correspond in polynomial time.

## Expansion

Characterization: in a BTP each internal node with its two children is a triangle; distinct internal nodes give distinct peaks, and every non-root node is a child of exactly one internal node, so these $q-1$ triangles are conflict-free. Conversely, $q-1$ conflict-free triangles have $2q-2$ pairwise distinct tails, so exactly one element of $L$ is not a tail; call it the root and make each tail a child of its triangle's peak. Every non-root node then has exactly one parent, every node has $0$ or $2$ children, and since weights are positive a peak is strictly heavier than its tails, so the parent relation has no cycles and defines a complete rooted binary tree satisfying CSP. The bound $q-1$ follows because conflict-free triangles use disjoint pairs of tails among $2q-1$ elements.

Reduction: modulo $4(m+1)$ the elements $\hat x_i, \hat y_i, \hat b_i, \beta_j$ are congruent to $1, 3, 4, 4j$ respectively. A node $\hat x_i$ is never the root: the residues force the sibling of each $\hat y$ to be an $\hat x$, so if an $\hat x$ were the root, the $m$ non-root $\hat y$'s would need $m$ distinct $\hat x$ siblings while only $m - 1$ remain. So its sibling $s$ and parent $p$ satisfy $\hat x_i + s = p$; the residues force $s = \hat y_{\alpha(i)}$ and $p = \hat b_{\gamma(i)}$, and since each element appears once, $\alpha, \gamma$ are permutations that solve the matching instance. In the other direction, the triangles $(\hat b_i, \{\hat x_{\pi_X(i)}, \hat y_{\pi_Y(i)}\})$ together with the chain $(\beta_{i+1}, \{\beta_i, \hat b_{i+1}\})$ for $1 \le i \le m-1$ (writing $\beta_1 := \hat b_1$) are $2m-1$ conflict-free triangles, hence a binary tree partition rooted at $\beta_m$.

## Sources

- I. Hajirasouliha, A. Mahmoody, B. J. Raphael, "A combinatorial approach for analyzing intra-tumor heterogeneity from high-throughput sequencing data", Bioinformatics (2014), Section 2 (Definitions 1 and 2), Section 3 (Theorems 3, 4 and 5 with proof) and Section 4 (Theorem 6), <https://doi.org/10.1093/bioinformatics/btu284>, PMCID PMC4058927.
