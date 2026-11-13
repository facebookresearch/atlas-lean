/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.Order
import Code.Correctness.SortSliceRange
import Code.Transcription.MergeAt

/-!
# Shared semantic precondition for both merge directions

`merge_lo` and `merge_hi` consume the same two post-trimming runs.  Their
physical movement directions differ, but the mathematical facts supplied by
`merge_at` do not.  This structure is therefore the single predicate shape
used by both local correctness proofs.

Comparator binding and canonical occurrence stability are deliberately not
fields here.  They are independent, explicit premises of both public merge
correctness theorems.
-/

namespace CPythonListsort

universe u v

variable {alpha : Type u} {nu : Type v}

/-- The complete run-local facts established by `merge_at` after its two
trimming gallops and consumed symmetrically by either merge direction. -/
structure MergeSemanticPre
    (lt : BoolComparator alpha)
    (call : MergeAtCall (Occurrence alpha) nu) : Prop where
  leftNonempty : 0 < call.na
  rightNonempty : 0 < call.nb
  leftSorted :
    Sorted (occurrenceComparator lt)
      (sortSliceRangeKeys call.state.data call.ssa.toNat call.na)
  rightSorted :
    Sorted (occurrenceComparator lt)
      (sortSliceRangeKeys call.state.data call.ssb.toNat call.nb)
  firstStrict :
    ∃ firstLeft firstRight,
      call.state.data.read? call.ssa = some firstLeft ∧
      call.state.data.read? call.ssb = some firstRight ∧
      lt firstRight.key.value firstLeft.key.value = true
  lastStrict :
    ∃ lastLeft lastRight,
      call.state.data.read?
          (call.ssa + Int.ofNat (call.na - 1)) = some lastLeft ∧
      call.state.data.read?
          (call.ssb + Int.ofNat (call.nb - 1)) = some lastRight ∧
      lt lastRight.key.value lastLeft.key.value = true

end CPythonListsort
