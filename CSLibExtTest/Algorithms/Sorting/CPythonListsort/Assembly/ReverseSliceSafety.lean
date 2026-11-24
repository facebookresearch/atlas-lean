/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Algorithms.Sorting.CPythonListsort.Assembly.ReverseSliceSafety

/-! # Fixed-input Listsort regressions -/

namespace CPythonListsort

/-! ## Branch and failure anti-vacuity regressions -/

private def reverseRegressionSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 0, value := some 10 },
        { key := 1, value := some 11 },
        { key := 2, value := some 12 },
        { key := 3, value := some 13 }] }

private def reverseNoValuesRegressionSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 0, value := none },
        { key := 1, value := none },
        { key := 2, value := none },
        { key := 3, value := none }] }

/-- An empty range succeeds without an access or fuel marker.  This is the
Lean model's deliberate totalization, not a reachable call of the C body. -/
private theorem sortsliceReverseTraced_empty_regression :
    (sortsliceReverseTraced? true reverseRegressionSlice 2 0).result.map
        (fun result => (result.fuelExhausted, result.slice.entries.toList)) =
      some (false, reverseRegressionSlice.entries.toList) ∧
    (sortsliceReverseTraced? true reverseRegressionSlice 2 0).trace =
      AccessTrace.empty := by
  decide

/-- The totalized empty range is also safe at the one-past endpoint admitted
by `RangeInBounds`; no attempted dereference is fabricated. -/
private theorem sortsliceReverseTraced_empty_one_past_regression :
    (sortsliceReverseTraced? true reverseRegressionSlice 4 0).result.map
        (fun result => (result.fuelExhausted, result.slice.entries.toList)) =
      some (false, reverseRegressionSlice.entries.toList) ∧
    (sortsliceReverseTraced? true reverseRegressionSlice 4 0).trace =
      AccessTrace.empty := by
  decide

/-- A singleton range also performs no access. -/
private theorem sortsliceReverseTraced_singleton_regression :
    (sortsliceReverseTraced? true reverseRegressionSlice 1 1).result.map
        (fun result => (result.fuelExhausted, result.slice.entries.toList)) =
      some (false, reverseRegressionSlice.entries.toList) ∧
    (sortsliceReverseTraced? true reverseRegressionSlice 1 1).trace =
      AccessTrace.empty := by
  decide

/-- An odd reversal swaps only its endpoints; the center cell is unchanged and
never appears in either physical phase's access trace. -/
private theorem sortsliceReverseTraced_odd_center_regression :
    (sortsliceReverseTraced? true reverseRegressionSlice 0 3).result.map
        (fun result => (result.fuelExhausted, result.slice.entries.toList)) =
      some
        (false,
          [{ key := 2, value := some 12 },
           { key := 1, value := some 11 },
           { key := 0, value := some 10 },
           { key := 3, value := some 13 }]) ∧
    (sortsliceReverseTraced? true reverseRegressionSlice 0 3).trace.accesses.map
        (fun event => (event.kind, event.region, event.index)) =
      [(.read, .inputKeys, 0), (.read, .inputKeys, 2),
       (.write, .inputKeys, 0), (.write, .inputKeys, 2),
       (.read, .synchronizedValues, 0), (.read, .synchronizedValues, 2),
       (.write, .synchronizedValues, 0), (.write, .synchronizedValues, 2)] := by
  decide

/-- A concrete no-values execution reverses the paired snapshot while emitting
only key-array events, pinning the source's `if (values != NULL)` guard. -/
private theorem sortsliceReverseTraced_no_values_regression :
    (sortsliceReverseTraced? false reverseNoValuesRegressionSlice 0 4).result.map
        (fun result => (result.fuelExhausted, result.slice.entries.toList)) =
      some
        (false,
          [{ key := 3, value := none },
           { key := 2, value := none },
           { key := 1, value := none },
           { key := 0, value := none }]) ∧
    (sortsliceReverseTraced? false reverseNoValuesRegressionSlice 0 4).trace.accesses.all
        (fun event => event.region = .inputKeys) = true := by
  decide

/-- A concrete two-swap values-mode execution reverses the data and records
the complete key phase before the complete synchronized-values phase. -/
private theorem sortsliceReverseTraced_two_swap_regression :
    (sortsliceReverseTraced? true reverseRegressionSlice 0 4).result.map
        (fun result => (result.fuelExhausted, result.slice.entries.toList)) =
      some
        (false,
          [{ key := 3, value := some 13 },
           { key := 2, value := some 12 },
           { key := 1, value := some 11 },
           { key := 0, value := some 10 }]) ∧
    (sortsliceReverseTraced? true reverseRegressionSlice 0 4).trace.accesses.map
        (fun event => (event.kind, event.region, event.index)) =
      [(.read, .inputKeys, 0), (.read, .inputKeys, 3),
       (.write, .inputKeys, 0), (.write, .inputKeys, 3),
       (.read, .inputKeys, 1), (.read, .inputKeys, 2),
       (.write, .inputKeys, 1), (.write, .inputKeys, 2),
       (.read, .synchronizedValues, 0), (.read, .synchronizedValues, 3),
       (.write, .synchronizedValues, 0), (.write, .synchronizedValues, 3),
       (.read, .synchronizedValues, 1), (.read, .synchronizedValues, 2),
       (.write, .synchronizedValues, 1), (.write, .synchronizedValues, 2)] := by
  decide

/-- The otherwise unreachable zero-fuel active arm returns the raw exhausted
result and also marks exhaustion in the trace. -/
private theorem reverseSlicePhaseLoopTraced_zero_fuel_regression :
    (reverseSlicePhaseLoopTraced? 0 .keys reverseRegressionSlice 0 1).result.map
        (fun result => result.fuelExhausted) = some true ∧
    (reverseSlicePhaseLoopTraced? 0 .keys reverseRegressionSlice 0 1).trace.fuelExhausted =
      true := by
  decide

/-- A reversed half-open interval is rejected before any access. -/
private theorem reverseSliceTraced_reversed_range_failure_regression :
    (reverseSliceTraced? reverseRegressionSlice 3 2).result = none ∧
    (reverseSliceTraced? reverseRegressionSlice 3 2).trace = AccessTrace.empty := by
  decide

/-- A past-the-end endpoint remains observable: the valid left read precedes
the rejected right read, whose recorded extent is the actual backing size. -/
private theorem reverseSliceTraced_oob_failure_regression :
    (reverseSliceTraced? reverseRegressionSlice 0 5).result = none ∧
    (reverseSliceTraced? reverseRegressionSlice 0 5).trace.accesses =
      [{ kind := .read, region := .inputKeys, index := 0, extent := 4 },
       { kind := .read, region := .inputKeys, index := 4, extent := 4 }] ∧
    ¬(reverseSliceTraced? reverseRegressionSlice 0 5).trace.allAccessesInBounds := by
  decide

end CPythonListsort
