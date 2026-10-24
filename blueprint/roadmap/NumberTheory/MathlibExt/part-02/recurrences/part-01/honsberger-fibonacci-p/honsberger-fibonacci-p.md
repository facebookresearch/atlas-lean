---
article_id: af_64d6bf9c8ba2ce03350e5fdc
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.honsberger_fibonacciP
---

# Honsberger fibonacci P

Honsberger identity for Fibonacci `p`-numbers. Binds source lines 425-449
with source-text SHA-256 `754dee8cf3e11595590ad2539aee76a3ad6d7ffcb80282b6a4488271f6392bd9`.
From `https://cs.uwaterloo.ca/journals/JIS/VOL27/Kuhapatanakul/kuha13.tex`,
source-file SHA-256 `dad9ca89271449561bda39a96e5705728a24469f6106405f6b2cc021c3d16524`,
stable ID `jis_grounded_9dbbcac802edaa76c96bd1ff`. Corrected accounting:
2 mentions / 1 paper / 1 proof use. Excludes the downstream generalized
Leonardo identity and the separate finite-sum identity. The hypotheses make
the initial values and recurrence part of the Lean proposition.

Proof: The definition follows Kuhapatanakul et al., JIS 27 (2024), lines 79-85; the identity cited
at lines 425-449 follows from a uniform recurrence and strong induction on `m` with a telescoping
base case.

## Depends on

- [Fibonacci P](fibonacci-p.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Recurrences.HonsbergerFibonacciP](../../../../../../../sources/v2/MathlibExt.md)
