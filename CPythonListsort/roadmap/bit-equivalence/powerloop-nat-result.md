---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.powerloopNatResult
---

# Natural quotient-bit recurrence result

Use the canonical zero-based quotient bits `((2^k * a) / n) % 2`, avoiding
ambiguity from dual binary expansions. For `0 < n ≤ PY_LIST_MAX` and exact
doubled midpoints satisfying `0 ≤ a < b < 2*n`, characterize the least `k` at
which the quotient bit of `a/n` is zero and that of `b/n` is one. Prove that the
natural-number recurrence stops within the 64-step bound and returns `k + 1`,
the one-based node power used by CPython. The theorem uses the project input
bound only to obtain a finite bit limit; it contains no finite-width execution
or C claim.

## Depends on

- [Natural-number powerloop specification](powerloop-nat-spec.md)
- [Finite-width implementation model](../transcription/word-model.md)

## Sources

- [CPython quotient-bit explanation](../../sources/listsort.md#the-merge-pattern)
- [Munro-Wild node power](../../sources/munro-wild-powersort-notes.md#node-power)
- [Selected platform and input domain](../../sources/toplevel-theorems.md#selected-platform-and-input-domain)
