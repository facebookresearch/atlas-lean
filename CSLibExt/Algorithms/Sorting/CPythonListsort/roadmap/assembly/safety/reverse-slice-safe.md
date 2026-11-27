---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.sortsliceReverse_safe
---

# Slice-reversal safety

For an exact `SortSlice.RangeInBounds` half-open slice, prove that
`reverse_slice` terminates without result- or trace-fuel exhaustion and every
paired endpoint read and write remains in bounds; lift the result to
`sortslice_reverse` for synchronized key/value slices. The public certificate
also returns an unchanged array extent, an unchanged explicit
`SortSlice.ValuesModeInvariant valuesPresent`, live temporary-payload accesses,
and an empty push trace.

The node also defines the traced reversal evaluator and proves that erasing its
trace yields exactly the reviewed `reverseSlice?`/`sortsliceReverse?` result on
the full raw model domain. Each physical phase produces the paired-snapshot
semantic reversal from the same pre-state: it is not a literal intermediate C
store and the key-phase result must not be fed into the values phase. The trace
nevertheless records the exact physical order: a complete key phase followed
by a complete values phase when that storage exists, and only the key phase
otherwise. A values phase is exposed as source-valid only when values storage
is present.

The complete `sortslice_reverse` theorem supplies the top-level initial
reversal. The completed top-level traced caller uses the public single-phase
theorem for the final reversal: `.values` in keyed mode (CPython reverses only
the saved values pointer there) and `.keys` in unkeyed mode.

The Lean evaluator deliberately totalizes an empty range, including one whose
base is the one-past endpoint. This is a model-domain extension, not a claim
about executing CPython's body on a zero-length range: the C body decrements
its exclusive high pointer before testing it, and every reviewed C call site
supplies a positive length.

## Depends on

- [Array-access trace model](access-trace.md)
- [Slice reversal](../../transcription/reverse-slice.md)
- [sortslice primitive safety](sortslice-safe.md)

## Sources

- [Verbatim `reverse_slice`](../../../sources/listobject-excerpts.md#reverse-slice)
- [Verbatim `sortslice_reverse`](../../../sources/listobject-excerpts.md#sortslice-reverse)
