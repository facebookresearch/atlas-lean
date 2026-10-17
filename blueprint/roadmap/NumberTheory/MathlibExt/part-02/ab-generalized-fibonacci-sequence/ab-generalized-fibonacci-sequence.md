---
article_id: af_be1badd9fc72544ddcedc818
declaration: structure
origin: cited
statement: formalized
lean: MetaMathlibExt.AbGeneralizedFibonacciSequence
---

# Ab Generalized Fibonacci Sequence

Kalman–Mena `(a, b)`-generalized Fibonacci sequence
(concept `jis_sem_34b8a222e3026d94d1de5306`;
source statement `jis_34b8a222e3026d94d1de5306`): real parameters `a`, `b`
together with a real-valued sequence satisfying `F 0 = 0`, `F 1 = 1`, the
recurrence `F (n + 2) = a * F (n + 1) + b * F n`, and the formal-power-series
identity for the ordinary generating series `x / (1 - a * x - b * x ^ 2)`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.AbGeneralizedFibonacciSequence](../../../../../sources/v2/MathlibExt.md)
