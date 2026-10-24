---
article_id: af_71d4230564b3df2ea5cb821e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.euler_product_mean_value
---

# Euler Product Mean Value

A coordinatewise multiplicative `f : (Fin k → ℕ) → ℂ` whose Moebius-convolution terms
over prime powers are summable has a mean value over cubes, given by the Euler product.

This is the Wintner–Ushiroya theorem (citing Ushiroya Thm. 4 and Tóth
Prop. 19) under the `Wanted` statement's hypothesis `hmult`, which asks for
`f (a * b) = f a * f b` whenever `a i` and `b i` are coprime for each `i`.
That is stronger than the source's multivariable multiplicativity
(`Nat.Coprime (∏ i, a i) (∏ i, b i)`): it forces `f n` to factor as a product
of one-variable multiplicative functions of the coordinates, and the proof
reduces to the one-variable Wintner theorem in each coordinate. The
summability hypothesis is `Σ_p Σ_{ν≠0} |(μ*f)(p^ν)|/p^{Σν} < ∞` with
`(μ*f)` spelled out as the divisor sum against `ArithmeticFunction.moebius`,
and the mean value is `Π_p (1 - 1/p)^k Σ_ν f(p^ν)/p^{Σν}`.
The cube averages are the diagonal of the source's multi-parameter limit,
so they converge to the same value.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Wintner Mean Value](wintner-mean-value.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.ArithmeticFunction.EulerProductMeanValue](../../../../../sources/v2/MathlibExt.md)
- László Tóth, "On the Asymptotic Density of k-tuples of Positive Integers with Pairwise Non-Coprime Components," Journal of Integer Sequences 27 (2024), Article 24.8.5, Theorem (unlabeled; multiplicative-function form following label Th_Wintner_gen), equation (label Euler_product), lines 314–326, https://cs.uwaterloo.ca/journals/JIS/VOL27/Toth/toth27.tex
