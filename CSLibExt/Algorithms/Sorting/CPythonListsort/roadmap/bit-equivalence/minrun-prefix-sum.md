---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.minrunPrefixSum
---

# Adaptive-minrun prefix-sum invariant

For `listSize.Nonnegative`, `listSize.toNat ≤ PY_LIST_MAX`, initialized
`mr_e < 32`, and `k ≤ 2^mr_e`, prove after `k` calls to `minrun_next` that the
emitted lengths sum to `(k * listSize.toNat) / 2^mr_e`, the stored residual is
`(k * listSize.toNat) % 2^mr_e`, the residual remains below `2^mr_e`, the next
addition stays below `2^63`, and every recorded assertion has passed. Those
facts are the loop invariant needed to invoke the conditional one-step equivalence. The
exponent premise is explicit in `minrunPrefixSum` at
`Code/Equivalence/MinrunResults.lean:470`. This exact prefix result
is not the output-band fact used by the top-level scan.

## Depends on

- [minrun_next](../transcription/minrun-next.md)
- [merge_init minrun initialization](../transcription/merge-init-minrun.md)

## Proof depends on

- [minrun_next quotient-remainder equivalence](minrun-next-equivalence.md)
- [merge_init exponent characterization](minrun-exponent-characterization.md)

## Sources

- [CPython integer generator](../../sources/listsort.md#computing-minrun)
- [Verbatim `minrun_next`](../../sources/listobject-excerpts.md#minrun-next)
