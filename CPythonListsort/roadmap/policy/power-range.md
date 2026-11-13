---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.powerRange
---

# Power range bound

For valid adjacent nonempty runs with total length `n ≤ PY_LIST_MAX`, let
`power` be the result of the transcribed `powerloop`. Prove the explicit bound
`1 ≤ power ∧ power ≤ B` for `B = 60`. Here
`PY_LIST_MAX = (2^63 - 1) / 8 = 2^60 - 1`, while the selected platform has
`MAX_MERGE_PENDING = 64`, so
`B + 1 = 61 < MAX_MERGE_PENDING`.

The upper-bound proof tracks the exact doubled-midpoint gap
`b - a = n1 + n2 ≥ 2`. Every iteration that does not stop leaves both
residues on the same side of `n` and doubles that gap; with
`n ≤ 2^60 - 1`, the 60th comparison must distinguish them. Consequently a
strictly increasing powered prefix contains at most 60 runs, and adding the
single newest run whose power is not yet computed gives depth at most 61.
This theorem uses only run positions and lengths.

## Depends on

- [Finite-width implementation model](../transcription/word-model.md)
- [powerloop](../transcription/powerloop.md)

## Proof depends on

- [powerloop terminating-result characterization](../bit-equivalence/powerloop-result.md)

## Sources

- [CPython stack and power discussion](../../sources/listsort.md#the-merge-pattern)
- [Verbatim `powerloop`](../../sources/listobject-excerpts.md#powerloop)
- [Selected platform and input domain](../../sources/toplevel-theorems.md#selected-platform-and-input-domain)
