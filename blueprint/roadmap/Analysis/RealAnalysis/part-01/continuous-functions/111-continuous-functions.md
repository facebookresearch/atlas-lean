---
article_id: af_11429b26dd813fea1e686935
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ContinuousFunctions.continuous_at_iff_eps_delta
---

# Definition (Continuous Functions) (2)

Let $S\subset \mathbb{R}$ and let $c\in S$. We say $f$ is continuous at $c$ if $\forall \epsilon>0$ $\exists\delta>0$ such that if $x\in S$ and $|x-c|\lt \delta$ then $|f(x) - f(c)|< \epsilon$. We say $f$ is continuous on $U$ for $U\subset S$ if $f$ is continuous at every point in $U$.

## Depends on

- [Definition (Set Relations) (Basic Set Theory) (1)](../basic-set-theory/001-set-relations.md)

## Sources

- [MIT 18.100A Real Analysis (Fall 2020), Continuous Functions](../../../../../sources/v1/RealAnalysis.md)
