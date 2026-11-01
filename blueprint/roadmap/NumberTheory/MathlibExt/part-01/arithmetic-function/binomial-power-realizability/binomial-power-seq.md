---
article_id: af_1b9bf652b0481b6ca0fad028
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.binomialPowerSeq
---

# Binomial Power Seq

Realizability of binomial-power sequences (Apéry, Delannoy, Franel).

`binomialPowerSeq r s n = ∑_k C(n,k)^r C(n+k,k)^s` over `k ≤ n`, whose
specializations include the Apéry numbers (`r = s = 2`), central Delannoy
numbers (`r = s = 1`), and Franel numbers of order `r` (`s = 0`).
`doldRealizable` is the Möbius criterion: `(μ*a)(n)` is non-negative and
divisible by `n` for all `n ≥ 1`. The wanted theorem is realizability for
every `s ≥ 0` and `r ≥ 1`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.ArithmeticFunction.BinomialPowerRealizability](../../../../../../sources/v2/MathlibExt.md)
- Geng-Rui Zhang, "Realizability of Some Combinatorial Sequences," Journal of Integer Sequences 27 (2024), Article 24.3.3, Theorem (label Thm1.13), lines 143–144, https://cs.uwaterloo.ca/journals/JIS/VOL27/Zhang/zhang9.tex with `A(n,r,s)` at lines 120–122 (label Def1.5) and realizability at lines 86–93 (label Def1.1).
