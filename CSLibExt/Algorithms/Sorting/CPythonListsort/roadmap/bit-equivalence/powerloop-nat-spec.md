---
declaration: structure
origin: bridged
statement: formalized
lean: CPythonListsort.PowerloopNatState
---

# Natural-number `powerloop` specification

Define `PowerloopNatState`, the arbitrary-precision step and bounded loop, and
the exact doubled-midpoint initialization used by `powerloopNatSpec`. Define
the zero-based quotient bit `((2^k * a) / n) % 2` and the predicate saying
that `k` is the least index where the left bit is zero and the right bit is
one. CPython's returned node power is the corresponding one-based value
`k + 1`. These definitions contain no finite-width execution or C claim.

## Depends on

No roadmap prerequisites.

## Sources

- [CPython quotient-bit explanation](../../sources/listsort.md#the-merge-pattern)
- [Munro-Wild node power](../../sources/munro-wild-powersort-notes.md#node-power)
