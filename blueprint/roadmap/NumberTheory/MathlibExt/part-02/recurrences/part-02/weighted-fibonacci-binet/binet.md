---
article_id: af_67133f4fde895e76fe3d58c9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.binet
---

# Binet

Weighted `r`-generalized Fibonacci Binet asymptotics with ratio limit: there is
`C > 0` with `a n = C * lam ^ n + o(lam ^ n)`, and `a (n+1) / a n → lam`.
Zero-based `a : ℕ → ℝ` corresponds to one-based `a_{n+1}`; `c`, `A : Fin r → ℝ`
correspond to `c_{k+1}`, `A_{k+1}`; `ha_init` and `ha_rec` encode
`a_n = c_n` for `n = 1, ..., r` and `a_n = ∑ A_k a_{n-k}` for `n > r`. The
dominant-root assumptions (`hlam_pos`, `hlam_root`, `hlam_simple`, `hlam_dom`)
encode the source's "dominant root, a simple positive root of the
characteristic polynomial."

## Depends on

This node has no prerequisites.

## Proof depends on

- [Binet general](binet-general.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Recurrences.WeightedFibonacciBinet](../../../../../../../sources/v2/MathlibExt.md)
- Passawan Noppakaew and Thanakorn Prinyasart, "Complete Sequences of Weighted r-Generalized Fibonacci Powers," Journal of Integer Sequences 24 (2021), Article 21.5.4, Proposition (label `binet`), lines 119–126, https://cs.uwaterloo.ca/journals/JIS/VOL24/Prinyasart/prin3.tex Proves `Wanted` entry `binet`. It follows from `binet_general`; the hypotheses `hlam_simple` and `hlam_dom` are unused and keep the source's shape.
