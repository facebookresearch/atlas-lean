---
article_id: af_2df0506c9be075d5cfd17215
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.fibonacciFactorial
---

# Fibonacci Factorial

Fibonacci factorial: `F_n! = F_n * F_{n-1} * ... * F_2 * F_1`,
with the empty convention `F_0! = 1`. Values are in `ℚ` so the source
ratios are not distorted by `Nat` truncating division. Uses `Nat.fib`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.GeneralizedFibocatalanNumber](../../../../../sources/v2/MathlibExt.md)
