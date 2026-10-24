---
article_id: af_01f93c5d7d033456f097068c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: weierstrass_m_test
---

# Theorem (Weierstrass M-test) (Sequences of Function, Pointwise and Uniform Convergence) (1)

Let $f_j:S\to \mathbb{R}$ and suppose $\exists M_j>0$ such that a) $\forall x\in S$, $|f_j(x)|\leq M_j$, and b) $\sum_{j=1}^\infty M_j$ converges. Then, 1. $\forall x\in S$, $\sum_{j=1}^\infty f_j(x)$ converges absolutely. 2. Let $f(x) = \sum_{j=1}^\infty f_j(x)$ for $x\in S.$ Then, $\sum_{j=1}^n f_j\to f$ uniformly on $S$.

## Depends on

- [Definition (Series) (1)](../../part-01/series/032-definition.md)
- [Definition (Uniform Convergence) (Sequences of Function, Pointwise and Uniform Convergence) (1)](088-uniform-convergence.md)
- [Definition (Series section)](../../part-01/series/097-definition.md)

## Proof depends on

- [Theorem (Comparison Test) (Convergence tests) (1)](../../part-01/convergence-tests/034-comparison-test.md)

## Sources

- [MIT 18.100A Real Analysis (Fall 2020), Sequences of Function, Pointwise and Uniform Convergence](../../../../../sources/v1/RealAnalysis.md)
