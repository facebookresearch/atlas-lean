# Infinite Littlestone trees

Let $H \subseteq \{0,1\}^X$. A **Littlestone tree** for $H$ of depth $d \le \infty$ is a family $\{x_u : u \in \{0,1\}^k, 0 \le k < d\}$ of points of $X$ indexed by the nodes of the complete binary tree, such that for every finite $k \le d$ and every path $y = (y_1, \dots, y_k) \in \{0,1\}^k$ there exists $h \in H$ with

$$
h(x_{y_1 \cdots y_{i-1}}) = y_i \quad \text{for all } 1 \le i \le k .
$$

The class has an **infinite Littlestone tree** if such a family exists with $d = \infty$, that is, every finite branch of an infinite complete binary tree is realized by some concept. The Littlestone dimension is the supremum of the depths of finite Littlestone trees; an infinite Littlestone tree forces infinite Littlestone dimension, but the converse fails in general (a class may have Littlestone trees of every finite depth and no infinite one).

## Sources

- O. Bousquet, S. Hanneke, S. Moran, R. van Handel, A. Yehudayoff, "A Theory of Universal Learning", STOC (2021), arXiv:2011.04483.
