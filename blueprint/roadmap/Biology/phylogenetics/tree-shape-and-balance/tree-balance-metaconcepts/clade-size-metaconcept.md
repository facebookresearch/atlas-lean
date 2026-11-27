# Clade size metaconcept and its extremal trees

Let $\mathcal{T}^\ast_n$ be the set of rooted tree shapes with $n$ leaves (no vertex of out-degree one) and $\mathcal{BT}^\ast_n\subseteq\mathcal{T}^\ast_n$ the binary ones. For an inner vertex $v$ let $n_v$ be its clade size, the number of leaves below $v$. For $f:\mathbb{R}\to\mathbb{R}$ the (first-order) **clade size metaconcept** is

$$\Phi^{\mathcal{N}}_f(T)=\sum_{v\ \text{inner}} f(n_v).$$

With $f(x)=x$ this is the Sackin index, since $\sum_{v\ \text{inner}} n_v$ equals the sum of leaf depths. Call $f$ 2-positive if $f(x)>0$ for all $x\ge 2$. Let $T^{cat}_n$, $T^{fb}_h$, $T^{mb}_n$ and $T^{star}_n$ be the caterpillar, the fully balanced tree with $n=2^h$, the maximally balanced tree (every inner vertex has children with clade sizes differing by at most one) and the star tree.

1. If $f$ is (strictly) increasing, $T^{cat}_n$ (uniquely) maximizes $\Phi^{\mathcal{N}}_f$ on $\mathcal{BT}^\ast_n$; if $f$ is also 2-positive it does so on $\mathcal{T}^\ast_n$. The maximum value is $\sum_{i=2}^n f(i)$.
2. $\Phi^{\mathcal{N}}_f$ is an imbalance index on $\mathcal{BT}^\ast_n$ when $f$ is strictly increasing and either strictly concave, strictly convex, or affine $f(x)=mx+a$ with $m>0$. On $\mathcal{T}^\ast_n$ the same holds if $f$ is additionally 2-positive (concave and convex cases) or $a\ge 0$ (affine case).
3. If $f$ is strictly increasing and strictly convex, $T^{mb}_n$ is the unique minimizer on $\mathcal{BT}^\ast_n$. If $f$ is affine with $m>0$, the minimizers on $\mathcal{BT}^\ast_n$ are exactly the Sackin minimizers: $T^{fb}_{h_n}$ or trees whose leaves have only the depths $h_n-1$ and $h_n$, $h_n=\lceil\log_2 n\rceil$.
4. For every 2-positive $f$ (not necessarily increasing), $T^{star}_n$ is the unique minimizer on $\mathcal{T}^\ast_n$.

## Expansion

Maximization uses the componentwise order of sorted sequences: the caterpillar's sorted clade sizes $(2,3,\dots,n)$ dominate those of any binary tree, and a non-binary tree can be resolved step by step into a binary one without decreasing any entry. For strictly convex $f$ the proof is a local exchange argument in the style of the total cophenetic index: by locality, a minimizer cannot contain a vertex whose children are a leaf and a non-cherry, nor two sibling subtrees whose grandchild clade sizes can be swapped to equalize them, which forces every vertex to be balanced. The star tree minimizes on arbitrary trees because it has only the root as inner vertex and every other tree adds positive terms.

## Depends on

- [Balance value metaconcept and its extremal trees](balance-value-metaconcept.md)

## Sources

- Mareike Fischer, Tom Niklas Hamann, Kristina Wicke, "Metaconcepts of rooted tree balance", *Bulletin of Mathematical Biology* 87(9) (2025), 134, Propositions 2.10, 3.15, 3.21, 3.22, 3.23, Theorem 3.17, Corollaries 3.16 and 3.20, <https://doi.org/10.1007/s11538-025-01509-y> (preprint arXiv:2506.08614).
