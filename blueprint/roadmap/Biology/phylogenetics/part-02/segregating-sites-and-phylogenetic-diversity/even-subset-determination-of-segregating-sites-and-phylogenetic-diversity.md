# Even-subset determination of segregating sites and phylogenetic diversity

Let $X$ be a finite set of taxa and consider bi-allelic sites with states $0,1$. For $A \subseteq X$ let $p_A$ be the probability that a site has state 1 exactly on $A$ (any probabilities with $\sum_A p_A = 1$), and $\tilde p_A = (p_A + p_{X \setminus A})/2$. A site **segregates** over $A$ if it is not constant on $A$, so the probability of segregation over $A$ is

$$
s_A = \sum_{B \in \mathcal{S}_A} \tilde p_B, \qquad \mathcal{S}_A = \{B \subseteq X : B \cap A \neq \emptyset,\ A \setminus B \neq \emptyset\},
$$

with $s_A = 0$ when $|A| \le 1$. Dually, for a phylogenetic $X$-tree with branch lengths (or any split weight function $w$ on bipartitions $U|V$ of $X$), the **phylogenetic diversity** $\delta_A$ of $A$ is the total length of the smallest subtree connecting $A$, and with $\tilde w_B = w_{B|X\setminus B}/2$

$$
\delta_A = \sum_{B \in \mathcal{S}_A} \tilde w_B .
$$

Let $\mathbb{T}_k$ be the tangent numbers, $\tanh x = \sum_{k \ge 0} \mathbb{T}_k x^k/k!$. Then:

1. Values on even subsets determine all values: for every $A \subseteq X$ of odd cardinality (Theorem 1 and its diversity analogue, Theorem 3)

$$
s_A = \sum_{\substack{B \subset A\\ |B| \text{ even}}} \frac{\mathbb{T}_{|A|-|B|}}{2^{|A|-|B|}}\, s_B, \qquad \delta_A = \sum_{\substack{B \subset A\\ |B| \text{ even}}} \frac{\mathbb{T}_{|A|-|B|}}{2^{|A|-|B|}}\, \delta_B .
$$

2. The symmetrized pattern probabilities and the split weights are recovered by Möbius-type inversion: for all nonempty $B \subsetneq X$ (Theorems 2 and 4)

$$
\tilde p_B = \frac{1}{2}\sum_{A \supseteq B} (-1)^{|A|-|B|+1} s_A, \qquad \tilde w_B = \frac{1}{2}\sum_{A \supseteq B} (-1)^{|A|-|B|+1} \delta_A .
$$

Theorems 2 and 4 print these inversions "for all $B\subseteq X$", but their proof covers only nonempty proper subsets, and the formulas fail at $B=X$ (the right-hand side is $-s_X/2\le0$, while $\tilde p_X=\frac12$ when every site is constant) and at $B=\emptyset$; the page restricts them accordingly.

Thus segregating-site probabilities have exactly the $2^{|X|-1}-1$ degrees of freedom of the symmetrized pattern probabilities, although there are $2^{|X|}-|X|-1$ subsets with at least two elements.

## Expansion

The two formulas $s_A = \sum_{B \in \mathcal{S}_A} \tilde p_B$ and $\delta_A = \sum_{B \in \mathcal{S}_A} \tilde w_B$ have the same shape, so every identity for one transfers to the other by relabelling. For three taxa the odd-size formula reads $s_{abc} = (s_{ab} + s_{ac} + s_{bc})/2$: a bi-allelic site segregating on three taxa splits them $1{+}2$ and segregates on exactly two of the three pairs; for diversity it is the familiar fact that the spanning tree of three leaves has half the length of the sum of the three pairwise distances. The tangent numbers arise from inclusion–exclusion over even and odd subsets. The pairwise diversity $\pi$ is the average of $s_A$ over two-element sets, so these identities connect $\pi$-type and higher-order segregation statistics to the same underlying split structure.

## Sources

- David Bryant, Steffen Klaere, The link between segregation and phylogenetic diversity, arXiv:1008.4625 (2010). <https://doi.org/10.48550/arXiv.1008.4625>. Published version: Journal of Mathematical Biology 64(1-2) (2012), 149–162, <https://doi.org/10.1007/s00285-011-0409-5>; locators above refer to the arXiv version.
