---
article_id: af_09a9220f00ce0fefccb2a29c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Integration.riemann_integral_convergence
---

# Theorem (Riemann Integral) (The Riemann Integral)

Let $f\in C([a,b])$. Then, there exists a unique number denoted $\int_a^b f(x)\,\mathrm{d}x\in \mathbb{R}$ with the following property: for all sequences of tagged partitions $\{(\underline{x}^r, \underline{\xi}^r)\}$ such that $\lVert \underline{x}^r\rVert \to 0$, we have $\lim_{r \to \infty} S_f(\underline{x}^r, \underline{\xi}^r) = \int_a^b f(x) \,\mathrm{d}x.$

## Depends on

- [Definition (Partition) (The Riemann Integral section)](065-partition.md)
- [Definition (Tag) (The Riemann Integral section)](066-tag.md)
- [Definition (Riemann sum) (The Riemann Integral section)](067-riemann-sum.md)
- [Definition (Sequence Convergence of Reals) (Sequences and Series, Sequences and Limits) (1)](../../part-01/sequences-and-series/022-sequence-convergence-of-reals.md)
- [Definition (C((a,b)))](064-a-b.md)

## Proof depends on

- [Definition (Modulus of Continuity) (The Riemann Integral section)](069-modulus-of-continuity.md)
- [Theorem I (The Riemann Integral section)](070-theorem-i.md)
- [Theorem III (The Riemann Integral section)](073-theorem-iii.md)
- [Theorem (Triangle Inequality) (The Uncountability of the Real Numbers section) (1)](../../part-01/the-uncountability-of-the-real-numbers/018-triangle-inequality.md)
- [Theorem (Squeeze Theorem) (Lecture 8, Facts About Limits)](../../part-01/lecture-8/026-squeeze-theorem.md)
- [Theorem (Cauchy Sequences section)](../../part-01/cauchy-sequences/090-theorem.md)

## Sources

- [MIT 18.100A Real Analysis (Fall 2020), The Riemann Integral](../../../../../sources/v1/RealAnalysis.md)
