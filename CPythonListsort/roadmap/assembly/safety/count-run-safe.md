---
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: CPythonListsort.countRun_safe
---

# `count_run` safety

For an exact `SortSlice.RangeInBounds slice base nremaining` range with
`0 < nremaining` and signed-size representability, and for any total Boolean
comparator, prove that every scan and operational-equivalence-block reversal
in `count_run` is in bounds and that the bounded loops return before result- or
trace-fuel exhaustion with a length in `1 .. nremaining`. Take
`SortSlice.ValuesModeInvariant state.a.hasValues slice` as an explicit premise
and return it for the resulting slice, using slice-reversal safety for every
block, prefix, and whole-run reversal.

The public postcondition exposes success/result equality, false result fuel,
false trace fuel, globally in-bounds accesses, live temporary-payload accesses,
an empty push trace, exact erasure, preserved values mode, unchanged backing
extent, and the returned-length bounds. Installing the returned slice in the
merge state has a separate frame theorem: temporary storage, pending runs,
comparator, list metadata, and adaptive counters are unchanged.

The node also defines the traced `count_run` evaluator and proves exact erasure
to `countRun?` on the complete raw model domain. Its helper trace is assembled
from the actual traced reads and traced reversal calls; no raw result is paired
with a separately manufactured trace. Named
order theorems retain predecessor-read then next-read composition, primary
`next < previous` branch priority, and descending scan -> trailing block
reversal -> whole-prefix reversal -> ascending-extension composition. This
Lean access order is an instrumentation choice, not a claim about C operand
evaluation order; the comparator orientation and control branches match the C
source.

Concrete regressions cover singleton and full-ascending runs (including no
endpoint reread), the reachable first/last gate, strict descending reversal,
a tagged operational-equivalence block with synchronized-values events before
the whole reversal, descending-to-ascending extension, an inconsistent
constant-true comparator demonstrating primary-branch priority, active
zero-fuel helper arms, the zero-length guard failure, and an out-of-bounds
modeled read. For the concrete `Nat.lt` tagged regression, operational
equivalence is ordinary key equality; making that interpretation and the
general stability conclusion requires the later strict-weak-order node.

The v1 comparator is a total `BoolComparator`, so CPython's comparator-error
`fail:` path is outside this model. The zero-length and out-of-bounds
regressions pin Lean model-domain assertion/access failures; they do not claim
to exercise CPython's comparator failure path.

## Depends on

- [Array-access trace model](access-trace.md)
- [count_run](../../transcription/count-run.md)
- [sortslice primitive safety](sortslice-safe.md)

## Proof depends on

- [Slice-reversal safety](reverse-slice-safe.md)

## Sources

- [Verbatim `count_run`](../../../sources/listobject-excerpts.md#count-run)
