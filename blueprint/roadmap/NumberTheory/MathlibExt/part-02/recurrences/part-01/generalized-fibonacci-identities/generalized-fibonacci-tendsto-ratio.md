---
article_id: af_211a311798694800793824e2
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.generalizedFibonacci_tendsto_ratio
---

# Generalized Fibonacci tendsto ratio

Ratio limit: for `p > 0` and a solution of `W (k + 2) = p * W (k + 1) + W k` with
`W 0 ≥ 0` and `W 1 > 0`, `W (k + 1) / W k` tends to the dominant root `(p + √(p ^ 2 + 4)) / 2`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Generalized Fibonacci binet](generalized-fibonacci-binet.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Recurrences.GeneralizedFibonacciIdentities](../../../../../../../sources/v2/MathlibExt.md)
