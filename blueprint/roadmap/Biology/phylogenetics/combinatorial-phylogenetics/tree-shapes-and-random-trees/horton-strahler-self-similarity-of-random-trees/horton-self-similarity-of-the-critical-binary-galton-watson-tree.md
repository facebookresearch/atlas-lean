# Horton self-similarity of the critical binary Galton–Watson tree

**Setting.** In a finite rooted binary tree, the **Horton–Strahler order** is defined from the leaves down: leaves have order 1, and an internal vertex whose two children have orders $i \ge j$ has order $i+1$ if $i = j$ and order $i$ otherwise. A **branch** of order $j$ is a maximal path of vertices of order $j$; a branch of order $j$ receives **side branches** of orders $i < j$. **Horton pruning** $\mathcal R$ deletes the leaves and their parental edges and suppresses degree-2 vertices, lowering every order by one. A measure on trees is **Horton self-similar** if it is invariant under pruning conditioned on non-emptiness, and **Tokunaga self-similar** with Tokunaga coefficients $T_k$ if the mean number of side branches of order $i$ on a branch of order $j$ is $T_{j-i}$. Let $N_j$ be the number of branches of order $j$.

**Theorem.**
1. (Characterization, Theorem 4) For a Galton–Watson tree with offspring law $\{q_k\}$, Horton self-similarity, mean Horton self-similarity and Tokunaga self-similarity are each equivalent to the critical binary law $q_0 = q_2 = 1/2$. That law has Tokunaga coefficients $T_k = 2^{k-1}$ and satisfies the strong Horton law with Horton exponent $R = 4$.
2. (Branch structure, Proposition 6) If $T \sim \mathcal{GW}(1/2,1/2)$, then its order is $\mathrm{Geom}_1(1/2)$; the number $m_j$ of side branches on a uniformly chosen branch of order $j \ge 2$ is $\mathrm{Geom}_0(2^{1-j})$, so $\mathbb E\,m_j = 2^{j-1} - 1 = T_1 + \cdots + T_{j-1}$; and given $m_j$, side branches have independent orders, equal to $i$ with probability $T_{j-i}/(T_1+\cdots+T_{j-1})$.
3. (Attraction, Theorem 5) If a Galton–Watson law is critical ($q_1 \ne 1$, $\sum_k kq_k = 1$) with bounded offspring, then the law of $\mathcal R^n(T)$ given $\mathcal R^n(T) \ne \emptyset$ converges to the critical binary Galton–Watson law.
4. (Uniform binary trees, Corollaries 2–3 and Theorem 8) For a uniformly random binary tree with $N$ leaves, $N_j/N \to 4^{-(j-1)}$ in probability for every $j$, and $\sqrt N\,(N_2/N - \frac14) \Rightarrow \mathcal N(0, 4^{-2})$.

$$\lim_{N\to\infty} \frac{N_{j+1}}{N_j} = \frac14, \qquad \mathbb E\, m_j = \sum_{k=1}^{j-1} 2^{k-1}.$$

## Expansion

Pruning the leaves of a critical binary Galton–Watson tree gives, conditionally on non-emptiness, another critical binary Galton–Watson tree, so the tree order is geometric and each pruning step reduces branch counts by the same factor $R = 4$. The attraction property explains why this law is universal among critical branching trees with bounded offspring: Horton pruning acts as a renormalization whose only fixed point is the critical binary law. Horton–Strahler orders and Tokunaga coefficients therefore give tree-shape statistics whose values under critical branching are known exactly.

## Sources

- Yevgeniy Kovchegov and Ilya Zaliapin, "Random self-similar trees: A mathematical theory of Horton laws", arXiv:1905.02629 (2019), section "Critical binary Galton–Watson tree", Theorems 4, 5 and 8, Proposition 6, Corollaries 2–3, <https://doi.org/10.48550/arXiv.1905.02629>. Published version: Probability Surveys 17 (2020) 1–213, <https://doi.org/10.1214/19-ps331>.
