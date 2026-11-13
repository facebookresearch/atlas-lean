---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.minrunInit_eq_spec
---

# `merge_init` exponent and conditional mask equivalence

For a nonnegative representable list length, prove that the finite-width
initialization takes the same branches as the arbitrary-precision exponent
recurrence. The unconditional bridge exports the stored exponent, zero
residual, and bounded-loop status as `minrunInit_exponent_eq_spec`
(`Code/Equivalence/Minrun.lean:105`). The exact-mask theorem
`minrunInit_eq_spec` additionally assumes that the selected exponent is below
32 (`Code/Equivalence/Minrun.lean:123`); under that premise the
selected 32-bit transcription mask equals the mathematical low-bit mask.

No exact-mask conclusion is claimed over the full admitted input domain. The
selected 32-bit word convention happens to retain the ideal all-ones mask at
the `mr_e = 32` fencepost, but the exported exact theorem intentionally uses
the simpler strict premise `mr_e < 32`; divergence can occur once
`mr_e > 32`. The stronger first-exponent and non-exhaustion facts belong to
the dedicated exponent-characterization node, while full-domain consumers use
the independent output-band node.

## Depends on

- [merge_init minrun initialization](../transcription/merge-init-minrun.md)

## Sources

- [CPython adaptive-minrun explanation](../../sources/listsort.md#computing-minrun)
- [Verbatim `merge_init`](../../sources/listobject-excerpts.md#merge-init)
