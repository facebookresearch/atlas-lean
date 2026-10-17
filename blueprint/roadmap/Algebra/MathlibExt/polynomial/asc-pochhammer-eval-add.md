---
article_id: af_1621f00bb1da7bb19d0dce52
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.ascPochhammer_eval_add
---

# Rising Factorial Binomial

Binomial theorem for rising factorials: `(a + b)` raised to the rising
`n`-th power expands as the choose-weighted sum of products of the rising
powers of `a` and `b`.

The source proves this by induction on `n`, using the Pascal recurrence;
verified computationally for `n = 0..8` over five real pairs `(a, b)`.
Proves `Wanted` entry `ascPochhammer_eval_add`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Algebra.Polynomial.RisingFactorialBinomial](../../../../sources/v2/MathlibExt.md)
- Paul Eloe and Catherine Kublik, "When Numerical Analysis Crosses Paths with Catalan and Generalized Motzkin Numbers," Journal of Integer Sequences 21 (2018), Article 18.8.4, Theorem (label binomthm_risingpoly), equation (label `binomial theorem`), lines 156–161, https://cs.uwaterloo.ca/journals/JIS/VOL21/Kublik/kublik2.tex
