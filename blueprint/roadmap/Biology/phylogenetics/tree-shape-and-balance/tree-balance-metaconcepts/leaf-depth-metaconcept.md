# Leaf depth metaconcept and its extremal trees

Let $\mathcal{T}^\ast_n$ be the rooted tree shapes with $n$ leaves and $\mathcal{BT}^\ast_n$ the binary ones. The depth $\delta_T(x)$ of a leaf $x$ is the number of edges from the root to $x$. For $f:\mathbb{R}\to\mathbb{R}$ the (first-order) **leaf depth metaconcept** is

$$\Phi^{\Delta}_f(T)=\sum_{x\ \text{leaf}} f\big(\delta_T(x)\big).$$

1. If $f(\delta)=m\delta+a$ then $\Phi^{\Delta}_f(T)=m\,S(T)+na$ with $S$ the Sackin index; for $m>0$ it is a (binary) imbalance index equivalent to the Sackin index.
2. If $f$ is strictly increasing and convex, $\Phi^{\Delta}_f$ is a (binary) imbalance index: the caterpillar is the unique maximizer and, for $n=2^h$, the fully balanced tree is the unique minimizer on $\mathcal{BT}^\ast_n$. For every $n$ its minimizers on $\mathcal{BT}^\ast_n$ coincide with the Sackin minimizers, namely the fully balanced tree of height $h_n=\lceil\log_2 n\rceil$ or the trees whose leaves have only the two depths $h_n-1$ and $h_n$.
3. If $f$ is (strictly) increasing, the star tree is the (unique) minimizer on $\mathcal{T}^\ast_n$.

## Expansion

A binary tree has Kraft sum $\sum_x 2^{-\delta_T(x)}=1$. Among depth profiles with this constraint, a convex increasing $f$ is minimized when the depths are as equal as possible, which forces all depths into $\{h_n-1,h_n\}$; this is the same set of trees that minimizes $\sum_x\delta_T(x)$. Maximization follows by resolving any tree toward the caterpillar, which increases leaf depths entrywise. In the star tree every leaf has depth $1$, the smallest possible.

## Depends on

- [Clade size metaconcept and its extremal trees](clade-size-metaconcept.md)

## Sources

- Mareike Fischer, Tom Niklas Hamann, Kristina Wicke, "Metaconcepts of rooted tree balance", *Bulletin of Mathematical Biology* 87(9) (2025), 134, Remark 3.29, Propositions 3.30, 3.31 and 3.32, <https://doi.org/10.1007/s11538-025-01509-y> (preprint arXiv:2506.08614).
