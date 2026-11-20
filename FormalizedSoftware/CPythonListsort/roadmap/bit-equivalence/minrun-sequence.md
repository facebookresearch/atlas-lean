---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.minrunSequence
---

# Balanced adaptive-minrun sequence

For `listSize.Nonnegative`, `listSize.toNat ≤ PY_LIST_MAX`, and initialized
`mr_e < 32`, define the first `2^mr_e` generated target lengths and prove one
theorem that their length is exactly `2^mr_e`, every entry is either the floor
or ceiling of `listSize.toNat / 2^mr_e`, their sum is `listSize.toNat`, the
residual returns to zero, and every recorded assertion has passed. The
premises are explicit in `minrunSequence` at
`Code/Equivalence/MinrunResults.lean:643`.

This is a conditional statement about the exact-arithmetic generator cycle,
not a full-domain property of the selected 32-bit transcription mask and not a claim that
`list_sort_impl` must discover exactly that many natural runs. No top-level
safety or correctness node consumes it; those chains use the unconditional
output-band theorem instead.

## Depends on

- [merge_init minrun initialization](../transcription/merge-init-minrun.md)
- [minrun_next](../transcription/minrun-next.md)

## Proof depends on

- [merge_init exponent characterization](minrun-exponent-characterization.md)
- [Adaptive-minrun prefix-sum invariant](minrun-prefix-sum.md)

## Sources

- [CPython adaptive-minrun explanation](../../sources/listsort.md#computing-minrun)
