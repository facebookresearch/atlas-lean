---
article_id: af_09afd6d1b6d112666f3fdf72
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: martingale_orthogonal_general
---

# Theorem (Orthogonality of martingale increments)

Let $X_n$ be a martingale with $E[X_n^2] < \infty$ for all $n$. If $m \leq n$ and $Y \in \mathcal{F}_m$ with $E[Y^2] < \infty$, then $E[(X_n - X_m) Y] = 0$.

## Depends on

- [Definition (Martingale, supermartingale, submartingale)](../../part-02/lecture-29/091-martingale-supermartingale-submartingale.md)

## Proof depends on

- [Definition (Conditional expectation)](../lecture-25/053-conditional-expectation.md)

## Sources

- [MIT 18.175 Theory of Probability (Spring 2014), Lecture 28](../../../../../sources/v1/TheoryOfProbability.md)
