---
article_id: af_37bb7a3dbcbbf297604c7021
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.wintner_mean_value_multivariable
---

# Wintner Mean Value Multivariable

Wintner's mean-value theorem for arithmetic functions of several variables.

Math notes: `mobiusConvolution` is the Dirichlet convolution `μ * f` over divisor tuples;
the hypothesis is absolute convergence of `Σ |(μ*f)(m)| / (m_1 ⋯ m_k)`, and the conclusion
is convergence of the rectangular mean to the corresponding infinite sum.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.ArithmeticFunction.WintnerMeanValueMultivariable](../../../../../sources/v2/MathlibExt.md)
- László Tóth, "On the Asymptotic Density of k-tuples of Positive Integers with Pairwise Non-Coprime Components," Journal of Integer Sequences 27 (2024), Article 24.8.5, Theorem `Th_Wintner_gen`, lines 300–311, <https://cs.uwaterloo.ca/journals/JIS/VOL27/Toth/toth27.tex>. Proved by H. Ushiroya (2012) as a generalization of Wintner's classical one-variable theorem.
