# Martinet's totally real towers

There is a real constant $C > 0$ such that for every
$N \in \mathbb{N}$ there exist a natural number $d \ge N$ and a totally real number field $K$ of
degree $[K : \mathbb{Q}] = d$ whose discriminant $\Delta_K$ satisfies $|\Delta_K| \le C^d$.

## Sources

- Theorem 3.2 of T. F. Bloom, W. Sawin, C. Schildkraut, D. Zhelezov, *The sum-product conjecture is false for real numbers*, arXiv:2605.28781. Lean axiom: https://github.com/mathlib-initiative/sum_product (SumProduct.exists_totallyReal_discr_le). Underlying result: J. Martinet, *Tours de corps de classes et estimations de discriminants*, Invent. Math. 44 (1978), 65–73. Problem `martinet_totally_real_towers` of the lean-eval benchmark.
