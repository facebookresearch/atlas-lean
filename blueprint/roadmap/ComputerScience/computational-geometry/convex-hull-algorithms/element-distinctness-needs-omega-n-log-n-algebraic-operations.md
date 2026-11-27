# Element distinctness needs Ω(n log n) algebraic operations

Every algebraic computation tree that decides, for $x_1, \dots, x_n \in \mathbb{R}$, whether $x_i \ne x_j$ for all $i \ne j$ has complexity $\Omega(n \log n)$. The set $W$ of inputs with pairwise distinct coordinates has $n!$ connected components, one for each ordering $x_{\sigma(1)} < \dots < x_{\sigma(n)}$, and $\log_2 n! = \Theta(n \log n)$.

## Depends on

- [Algebraic computation tree](algebraic-computation-tree.md)

## Proof depends on

- [Ben-Or's lower bound for algebraic computation trees](ben-or-s-lower-bound-for-algebraic-computation-trees.md)

## Sources

- M. Ben-Or, "Lower bounds for algebraic computation trees", *Proceedings of the 15th Annual ACM Symposium on Theory of Computing*, 1983, pp. 80–86, <https://doi.org/10.1145/800061.808735>: Theorem 1 (element distinctness) and Section 6 (the $n!$ components $\{x : x_{\sigma(1)} < \dots < x_{\sigma(n)}\}$)
