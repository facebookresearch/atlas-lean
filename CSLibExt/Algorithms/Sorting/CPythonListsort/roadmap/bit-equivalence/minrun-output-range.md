---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.minrunNextN_output_bounds
---

# Unconditional adaptive-minrun output band

For every positive nonnegative `listSize ≤ PY_LIST_MAX` and every natural
number of calls, prove that the transcribed 32-bit-mask generator initialized
by `merge_init` passes every recorded signed-overflow assertion and emits only
targets `target` satisfying

```text
1 ≤ target ≤ MAX_MINRUN = 64.
```

The main result is `minrunNextN_output_bounds` at
`Code/Equivalence/MinrunResults.lean:295`. Its companion
`minrunNext_after_init_bounds` at
`Code/Equivalence/MinrunResults.lean:309` packages the exact
one-step form consumed by the top-level scan after any reachable call prefix.
That consumption is explicit in `adaptiveMinrun_step_facts` at
`Code/Assembly/ListSortSupport.lean:270`.

The proof must not route through `minrunInit_eq_spec`, `minrunPrefixSum`, or
`minrunSequence`. Instead, use the exponent characterization to show that the
mathematical modulus lies below the positive list length and that the base
quotient is below 64; show separately that the actual zero-extended 32-bit
mask is strictly below that modulus; then preserve the current bound directly
through bitwise `and`. This makes the output band independent of exact
quotient/remainder equivalence once the mask truncates.

The kernel-checked executable regression
`minrun_cIntMask_truncation_regression` at
`Code/Equivalence/MinrunResults.lean:342` makes the distinction
observable: at exponent 33 its first two actual targets are `[63, 63]`, while
the ideal full-width trace emits `[63, 64]`. It uses kernel `decide`, not
`native_decide`, and is review evidence rather than a premise of the range
proof.

## Depends on

- [merge_init minrun initialization](../transcription/merge-init-minrun.md)
- [minrun_next](../transcription/minrun-next.md)
- [Finite-width implementation model](../transcription/word-model.md)

## Proof depends on

- [merge_init exponent characterization](minrun-exponent-characterization.md)

## Sources

- [Verbatim `merge_init`](../../sources/listobject-excerpts.md#merge-init)
- [Verbatim `minrun_next`](../../sources/listobject-excerpts.md#minrun-next)
- [CPython adaptive-minrun explanation](../../sources/listsort.md#computing-minrun)
- [Selected word-width and scope boundary](../../sources/toplevel-theorems.md#selected-platform-and-input-domain)
