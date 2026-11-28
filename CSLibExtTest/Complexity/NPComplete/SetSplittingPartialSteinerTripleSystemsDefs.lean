/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.SetSplittingPartialSteinerTripleSystemsDefs

namespace MetaMathlibExt.Complexity.NPComplete.SetSplittingPartialSteinerTripleSystems

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open SetSplitting (SetSplittingInstance SetSplittingFeasible)
open MathlibExt.Combinatorics.LinearTripleSystemIndependenceErdosProblem1024Wanted
  (IsLinearTripleSystem)

private theorem accepts_encoding (i : SetSplittingInstance) :
    setSplittingPartialSteinerTripleSystemsDec (bitEncode i) = true ↔
      WellFormed i ∧ SetSplittingFeasible i := by
  simp [setSplittingPartialSteinerTripleSystemsDec, bitDecode_bitEncode]

/-- Feasibility ranges over the finitely many subsets of `{0, ..., n - 1}`. -/
private theorem feasible_iff_powerset (i : SetSplittingInstance) :
    SetSplittingFeasible i ↔ ∃ S ∈ (Finset.range i.1).powerset,
      ∀ s ∈ i.2, (∃ x ∈ s, x ∈ S) ∧ ∃ y ∈ s, y ∉ S := by
  simp [SetSplittingFeasible, Finset.subset_iff]

/-- A lone continuation bit is a truncated instance encoding. -/
example : setSplittingPartialSteinerTripleSystemsDec [true] = false := by
  have h : bitDecode (α := SetSplittingInstance) [true] = none := rfl
  simp [setSplittingPartialSteinerTripleSystemsDec, h]

/-- The triples `{0, 1, 2}` and `{2, 3, 4}` meet in one point, and the part `{0, 3}` splits
both. -/
example :
    setSplittingPartialSteinerTripleSystemsDec
      (bitEncode ((5, [[0, 1, 2], [2, 3, 4]]) : SetSplittingInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨⟨by unfold SetSplitting.WellFormed; decide, ?_⟩, {0, 3}, by decide, by decide⟩
  unfold IsLinearTripleSystem tripleFamily
  decide

set_option maxRecDepth 20000 in
/-- The Fano plane is a Steiner triple system with no two-coloring of its points that splits
every line. -/
example :
    setSplittingPartialSteinerTripleSystemsDec
      (bitEncode ((7, [[0, 1, 2], [0, 3, 4], [0, 5, 6], [1, 3, 5], [1, 4, 6], [2, 3, 6],
        [2, 4, 5]]) : SetSplittingInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hf := ((accepts_encoding _).1 h).2
  rw [feasible_iff_powerset] at hf
  revert hf
  decide

/-- The triples `{0, 1, 2}` and `{0, 1, 3}` share two points, so they do not form a partial
Steiner triple system, although `{0}` splits both. -/
example :
    setSplittingPartialSteinerTripleSystemsDec
      (bitEncode ((4, [[0, 1, 2], [0, 1, 3]]) : SetSplittingInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hw := ((accepts_encoding _).1 h).1.2
  revert hw
  unfold IsLinearTripleSystem tripleFamily
  decide

end MetaMathlibExt.Complexity.NPComplete.SetSplittingPartialSteinerTripleSystems
