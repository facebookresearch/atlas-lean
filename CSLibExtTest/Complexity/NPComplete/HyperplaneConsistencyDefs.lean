/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.HyperplaneConsistencyDefs

namespace MetaMathlibExt.Complexity.NPComplete.HyperplaneConsistency

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : HyperplaneConsistencyInstance) :
    hyperplaneConsistencyDec (bitEncode i) = true ↔
      WellFormed i ∧ HyperplaneConsistencyFeasible i := by
  simp [hyperplaneConsistencyDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : hyperplaneConsistencyDec [true] = false := by
  have h : bitDecode (α := HyperplaneConsistencyInstance) [true] = none := rfl
  simp [hyperplaneConsistencyDec, h]

/-- In dimension one the threshold `0` with weight `1` puts the positive example `1` above and
the negative example `-1` below. -/
example :
    hyperplaneConsistencyDec
      (bitEncode ((1, [[(1, 0)]], [[(0, 1)]], 2) : HyperplaneConsistencyInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed intOf; decide, fun _ => 1, 0, ?_, ?_⟩
  · intro h
    simpa using congrFun h 0
  · simp [dot, intOf]

/-- The same vector `1` is both a positive and a negative example, so no hyperplane is consistent
with both, and `K = 2` is out of reach. -/
example :
    hyperplaneConsistencyDec
      (bitEncode ((1, [[(1, 0)]], [[(1, 0)]], 2) : HyperplaneConsistencyInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro hacc
  obtain ⟨-, w, w₀, -, hK⟩ := (accepts_encoding _).1 hacc
  by_cases h₁ : w₀ < dot w [(1, 0)] <;> by_cases h₂ : dot w [(1, 0)] < w₀ <;>
    simp [h₁, h₂] at hK
  exact lt_asymm h₁ h₂

/-- The no-instance above is well formed, so it is rejected for infeasibility. -/
example : WellFormed ((1, [[(1, 0)]], [[(1, 0)]], 2) : HyperplaneConsistencyInstance) :=
  by unfold WellFormed intOf; decide

end MetaMathlibExt.Complexity.NPComplete.HyperplaneConsistency
