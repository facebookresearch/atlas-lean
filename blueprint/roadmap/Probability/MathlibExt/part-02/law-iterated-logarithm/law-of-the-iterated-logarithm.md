---
article_id: af_ca5013242dad3e2c98a9bbdc
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Probability.LawIteratedLogarithmWanted.law_of_the_iterated_logarithm
---

# Law of the iterated logarithm

If `X : ℕ → Ω → ℝ` is i.i.d. with `Integrable`, `MemLp 2`, mean `0` and variance `1`, then a.s.
the normalized partial sums have `limsup = 1` and `liminf = -1` when divided by `√(2 n log log
n)`. Source: A. Y. Khinchin 1924, A. N. Kolmogorov 1929, P. Hartman and A. Wintner, On the law of
the iterated logarithm, Amer. J. Math. 63 (1941) 169–176; textbook in Durrett, Probability Theory
and Examples, 5th ed., Foundations of Modern Probability (Hartman-Wintner LIL). Lean i.i.d.
mean-zero variance-one normalized `√(2 n log log n)` form.

Proof: Hartman–Wintner truncation and exponential maximal bounds give the upper half; a CLT block
argument and the second Borel–Cantelli lemma give the lower half.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Law of the iterated logarithm of mem Lp](law-of-the-iterated-logarithm-of-mem-lp.md)

## Sources

- [MathlibExt, MathlibExt.Probability.LawIteratedLogarithm](../../../../../sources/v2/MathlibExt.md)
