---
article_id: af_c8c838f885f13b0310c9383b
declaration: def
origin: cited
statement: formalized
lean: RiemannStieltjes.IsBoundedVariation
---

# Definition 18.26

Let $f$ be a (real or complex valued) function defined on a nonempty real interval $[a, b]$. Then $f$ is of bounded variation if there exists a real number $M$ such that $$\sum_{i=0}^{n-1} |f(x_{i+1}) - f(x_i)| < M$$ for every partition $P = (x_0, \ldots, x_n)$ of $[a, b]$. If $f$ has a continuous derivative $f'$ on $[a, b]$ this is equivalent to requiring $\int_a^b |f'(x)|\,dx < \infty$. Every piecewise monotone function is of bounded variation. In particular, any step function with finitely many discontinuities on $[a, b]$ is of bounded variation.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 18.5](../../../../../../sources/v1/NumberTheoryI.md)
