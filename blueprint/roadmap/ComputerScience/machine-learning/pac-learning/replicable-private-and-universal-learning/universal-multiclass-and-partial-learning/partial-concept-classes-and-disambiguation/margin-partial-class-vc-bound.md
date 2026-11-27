# Margin-separable data as a partial class with VC and Littlestone dimension of order $R^2/\gamma^2$

Let $V$ be a real Hilbert space with $\dim V \ge R^2/\gamma^2$, where $0 < \gamma \le R$. A labelled sample $(x_1, y_1), \dots, (x_n, y_n) \in V \times \{0,1\}$ is **$(R,\gamma)$-separable** if all $x_i$ lie in some ball of radius $R$ and the convex hulls of $\{x_i : y_i = 1\}$ and $\{x_i : y_i = 0\}$ are at distance at least $2\gamma$. Let $H_{R,\gamma} \subseteq \{0,1,\star\}^V$ be the partial class of all $h$ such that every finite sample $(x_1, h(x_1)), \dots, (x_n, h(x_n))$ with $x_i \in \mathrm{supp}(h)$ is $(R,\gamma)$-separable. Then

$$
\mathrm{VC}(H_{R,\gamma}) = \Theta\big(R^2/\gamma^2\big) \quad\text{and}\quad \mathrm{LD}(H_{R,\gamma}) = \Theta\big(R^2/\gamma^2\big),
$$

independently of $\dim V$. The restriction $\gamma \le R$ matters: for $\gamma > R$ a single point with either label is still $(R,\gamma)$-separable, so the VC dimension stays at least $1$ while $R^2/\gamma^2 < 1$ can be arbitrarily small. Thus margin assumptions on the data, which are not realizability by a total class of halfspaces, are realizability by a partial class of finite VC and Littlestone dimension.

## Proof sketch

Since $\mathrm{VC} \le \mathrm{LD}$, it suffices to bound $\mathrm{LD}$ above and $\mathrm{VC}$ below. The Perceptron mistake bound shows that realizable sequences force at most $O(R^2/\gamma^2)$ mistakes, so $\mathrm{LD}(H_{R,\gamma}) = O(R^2/\gamma^2)$. For the lower bound, the points $R e_1, \dots, R e_k$ with $k = \lfloor R^2/\gamma^2 \rfloor \ge 1$ and $e_i$ orthonormal are shattered: for a partition into $A$ and $B$, the vector $w = \tfrac{\gamma}{R}\big(\sum_{i \in A} e_i - \sum_{i \in B} e_i\big)$ has norm at most $1$ and $\langle w, R e_i\rangle = \pm\gamma$, which separates the two convex hulls by distance at least $2\gamma$.

## Depends on

- [Partial concept classes and their VC and Littlestone dimensions](partial-concept-class.md)

## Proof depends on

- [Novikoff's perceptron mistake bound](../../../../online-learning-and-boosting/perceptron/mistakes-mul-sq-le.md)

## Sources

- N. Alon, S. Hanneke, R. Holzman, S. Moran, "A Theory of PAC Learnability of Partial Concept Classes", FOCS (2021), arXiv:2107.08444, Section 3.1, Definition 16 and Proposition 17.
