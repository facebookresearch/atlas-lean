---
article_id: af_66977359da54fd5a5aa12f3a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.wintner_mean_value
---

# Wintner Mean Value

Wintner mean-value theorem for arithmetic functions, one-variable case:
under absolute convergence of `Σ |(μ * f) n| / n`, the Cesàro mean
`x⁻¹ * Σ_{n ∈ [1, x]} f n` tends to `Σ' (μ * f) n / n`, where `μ * f` is the
Dirichlet convolution of the Möbius function with `f`.

Math notes: no multiplicativity, Euler product, quantitative error term, or
alternating mean is assumed or concluded.
Proves `Wanted` entry `wintner_mean_value`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.ArithmeticFunction.WintnerMeanValue](../../../../../sources/v2/MathlibExt.md)
- László Tóth, *On the Asymptotic Density of k-tuples of Positive Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27 (2024), Article 24.8.5, mean-value definition and Theorem `Th_Wintner_gen`, lines 292–310 (the `k = 1` case identified at lines 297–298 as Wintner's classical theorem; the source theorem itself is Ushiroya's multivariable generalization), <https://cs.uwaterloo.ca/journals/JIS/VOL27/Toth/toth27.tex>.
