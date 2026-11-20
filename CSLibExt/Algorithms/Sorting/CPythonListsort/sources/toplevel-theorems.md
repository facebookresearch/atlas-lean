# Project-authored top-level theorem contract

This document fixes the intended logical content of the two primary results.
Names and auxiliary definitions may be refined as the implementation model
matures, but weakening either conclusion requires explicit human approval.

The subject is a Lean model transcribed from CPython's pinned `listobject.c`.
The correspondence between that model and C is established by cited,
human-reviewed transcription, not by a machine-checked C refinement proof.

## Selected platform and input domain

Version one fixes a 64-bit CPython platform, including 8-byte `PyObject *`
pointers. CPython's list-allocation guard limits the pointer array to
`PY_SSIZE_T_MAX / sizeof(PyObject *)` entries. Accordingly, the model defines
`PY_LIST_MAX = (2^63 - 1) / 8` and admits input arrays only up to that length.
This is the source-backed slack that keeps `powerloop` midpoint arithmetic and
left shifts inside nonnegative signed `Py_ssize_t`.

One expression inside the 64-bit `MergeState` has a narrower source type:
the unsuffixed literal in `mr_mask = (1 << mr_e) - 1` makes the shift and
subtraction have C type `int`. The selected v1 platform additionally fixes
`int` at 32 bits. The transcription therefore evaluates that mask in
`BitVec 32` and zero-extends the resulting bit pattern into the 64-bit field.
Exact correspondence with CPython's arbitrary-precision design
note is exposed only under `mr_e < 32`; for larger selected exponents, the
top-level chains consume the separate theorem that every emitted target lies
in `1 .. MAX_MINRUN` instead of assuming an exact quotient/remainder cycle.

This word-level choice is not a claim about portable ISO C behavior. Signed
`1 << 31` is not representable as a positive 32-bit `int`, and shift counts at
least 32 are outside the operand width, so the source standard does not define
all executions admitted by the model's much larger list bound. The selected
zero-extended bit-vector behavior makes that boundary explicit. Compiler and
runtime behavior below C remain outside version one, and the public safety,
correctness, depth, and merge-cost conclusions do not depend on exact
high-exponent cycle equivalence.

The input-domain premise does not model allocation failure: it says the input
snapshot already exists and has a length that a selected-platform CPython list
can represent. Allocation attempts and their failure behavior remain outside
version one.

## Validated public input boundary

The raw transcription `listSortImpl?` intentionally keeps `hasKeyfunc`
separate from its paired-entry `SortSlice`, matching the C control-flow shape.
Raw refinement/erasure statements hold for that whole generalized domain, but
raw adequacy, safety, or correctness results must assume
`SortSlice.ValuesModeInvariant hasKeyfunc input` explicitly.

The public boundary is the proof-carrying `ListSortInput`. Its constructors
`ListSortInput.unkeyed` (canonical `PUnit` payload),
`ListSortInput.unkeyedAs` (an explicitly selected phantom payload type), and
`ListSortInput.keyed` establish the representation invariant from arrays. The
public `listSort?` wrapper delegates exactly to raw `listSortImpl?`. The public
traced evaluator implemented by the safety assembly is correspondingly
`listSortTraced?` over `ListSortInput`, with exact erasure to `listSort?`.
Neither public top-level theorem exposes a values-mode premise; it is carried
by the input. An explicit unkeyed `Array` corollary is required for each
user-facing result. Named keyed corollaries are also exported for direct API
discovery; they specialize the same general theorems and add no premise
(`Code/Correctness/ListSortCorrectness.lean:338` and
`Code/Assembly/ListSortSafety.lean:30`).

## Functional correctness

For a total Boolean comparator satisfying a strict weak order and either value
of CPython's `reverse` flag, `listsort` returns an array sorted by the requested
forward or argument-swapped relation, is a stable rearrangement of the input,
and contains exactly the input elements.

The implementation-level theorem consumes a validated `ListSortInput` (or a
raw input plus the explicit values-mode premise). The convenient theorem below
is the required unkeyed-array corollary, implemented through
`ListSortInput.unkeyed xs` and the public `listSort?` path rather than a direct
unvalidated call to `listSortImpl?`.

```lean
theorem listsort_correct
    (lt : α → α → Bool) (hwo : BoolStrictWeakOrder lt)
    (reverse : Bool) (xs : Array α) (h : xs.size ≤ PY_LIST_MAX) :
    let requestedLt := if reverse then fun a b => lt b a else lt
    let tagged := listsort lt reverse xs
    let ys := tagged.values
    Sorted requestedLt ys ∧ Stable requestedLt xs tagged ∧
      ys.toList.Perm xs.toList
```

The exact definitions of `BoolStrictWeakOrder`, `Sorted`, and `Stable` are part
of the model-design milestone. `BoolStrictWeakOrder` must reuse Mathlib's
Prop-valued strict-weak-order class through `lt a b = true`; `Stable` must
express occurrence-tagged equivalence-class stability, not merely the absence
of descending adjacent pairs. The modeled result retains those tags and
exposes its ordinary array through `.values`; this prevents an output from
being tagged retrospectively merely to satisfy the theorem.

Occurrence tags are ghost data, not a second implementation semantics. The
correctness chain must therefore prove an exact erasure equation: executing
`listSort?` on occurrence-tagged keys with `occurrenceComparator lt`, then
erasing every origin from the returned state, agrees with executing the same
validated input through the ordinary untagged `listSort? lt` evaluator. The
public theorem keeps the tagged execution equation as its stability witness
and also exports the ordinary untagged execution equation obtained through
that erasure theorem. A prose assertion that the evaluator never inspects tags
is not a substitute for this bridge.

## Comparator-independent safety

For every total Boolean comparator, including inconsistent comparators, and
every validated input within the selected 64-bit CPython list-allocation bound,
the model successfully returns a result without exhausting fuel, every recorded
indexed modeled array access is in bounds, and the maximum post-push pending-run
depth recorded by the trace is at most 61, strictly below
`MAX_MERGE_PENDING = 64`.

```lean
theorem listsort_safe
    (lt : κ → κ → Bool) (reverse : Bool)
    (input : ListSortInput κ ν)
    (h : input.slice.entries.size ≤ PY_LIST_MAX) :
    let execution := listSortTraced? lt reverse input
    (∃ result, execution.result = some result) ∧
      execution.trace.fuelExhausted = false ∧
      execution.trace.stackDepthMax ≤ 61 ∧
      61 < MAX_MERGE_PENDING ∧
      execution.trace.allAccessesInBounds
```

The required ordinary-array corollary specializes this theorem to
`input := ListSortInput.unkeyed xs`:

```lean
corollary listsort_safe_unkeyed
    (lt : α → α → Bool) (reverse : Bool) (xs : Array α)
    (h : xs.size ≤ PY_LIST_MAX) :
    let execution := listSortTraced? lt reverse (ListSortInput.unkeyed xs)
    (∃ result, execution.result = some result) ∧
      execution.trace.fuelExhausted = false ∧
      execution.trace.stackDepthMax ≤ 61 ∧
      61 < MAX_MERGE_PENDING ∧
      execution.trace.allAccessesInBounds
```

The model stores pending runs in an unbounded Lean `Array`. A push is a total
`Array.push`: it always changes the modeled state, and the trace records the
resulting depth after every push. In particular, forcing a push from depth 64
would produce depth 65 and record 65. `stackDepthMax` is the maximum of zero and
all recorded post-push depths; no record is filtered or clamped. There is no
guard that refuses that mutation and no event representing CPython's
debug-build assertion. Either choice would make the desired release-build
capacity property partly true by construction or would import behavior that is
not the property being proved. Instead, the strict recorded bound proves that
an admitted execution never even attempts the corresponding out-of-bounds
write to CPython's fixed C array.

The existential result conjunct is the completion claim; it rules out every
`none` failure arm. The separate `fuelExhausted = false` conjunct is the fuel
adequacy claim. Totality of the bounded Lean evaluator alone is not enough, and
termination must not be hidden behind `partial`. No order hypothesis may occur
in the policy or safety dependency chain.

Temporary merge storage has a separate representation invariant and lifecycle
obligation. Inline storage must fit the 256 raw pointer slots in `temparray`
(keyed logical cells consume two slots); heap storage must expose the same
one-or-two-slot multiplier used by `merge_getmem`; released storage may retain
stale `alloced` and values-mode metadata. In every valid top-level execution,
no temporary payload cell is read or written while backing is released,
although metadata may still be read. This liveness fact is discharged from the
transcribed `list_sort_impl` control flow and supplies the live-storage premise
used by the merge-loop safety lemmas; it is not a caller assumption.

Both the forward and reverse paths are in scope. Reverse mode is specified by
the argument-swapped strict relation; occurrence-level stability remains with
respect to the original input order.

## Explicit scope boundary

Version one models a pure total comparator and an immutable snapshot of
already-computed keys paired with payloads. Key-function evaluation,
exception-raising or stateful comparisons, mutation during sorting, allocator
failures, interpreter reentrancy, compiler correctness, and lower-level
runtime behavior are outside scope. The version-one claim is about the Lean model
and its reviewed correspondence to the selected C excerpts; it is not an
unconditional claim that every behavior of CPython's production sort has been
verified.

## Sources

- [Verbatim CPython list allocation guard](listobject-excerpts.md#list-resize)
- [CPython explanation of `powerloop` arithmetic slack](listsort.md#the-merge-pattern)
