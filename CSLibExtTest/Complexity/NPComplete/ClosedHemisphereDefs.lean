/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ClosedHemisphereDefs
-- Sums over `Fin 2` and linear arithmetic over `ℚ` for the infeasibility argument.
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

namespace MetaMathlibExt.Complexity.NPComplete.ClosedHemisphere

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : OpenHemisphere.OpenHemisphereInstance) :
    closedHemisphereDec (bitEncode i) = true ↔
      OpenHemisphere.WellFormed i ∧ ClosedHemisphereFeasible i := by
  simp [closedHemisphereDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : closedHemisphereDec [true] = false := by
  have h : bitDecode (α := OpenHemisphere.OpenHemisphereInstance) [true] = none := rfl
  simp [closedHemisphereDec, h]

open OpenHemisphere (OpenHemisphereInstance intOf)

/-- The vectors `(1, 0)`, `(0, 1)` and `(-1, -1)`. -/
private abbrev X : List (List (ℕ × ℕ)) := [[(1, 0), (0, 0)], [(0, 0), (1, 0)], [(0, 1), (0, 1)]]

/-- The direction `y = (1, 0)` has `x · y ≥ 0` for `(1, 0)` and `(0, 1)`. -/
example : closedHemisphereDec (bitEncode ((2, X, 2) : OpenHemisphereInstance)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold OpenHemisphere.WellFormed; decide,
    fun j => if j.val = 0 then 1 else 0, ?_, ?_⟩
  · intro h
    simpa using congrFun h 0
  · simp [intOf]

/-- The three vectors sum to `0`, so a nonzero `y` with `x · y ≥ 0` for all of them would have
all three products equal to `0`, forcing `y = 0`. -/
example : closedHemisphereDec (bitEncode ((2, X, 3) : OpenHemisphereInstance)) = false := by
  rw [Bool.eq_false_iff, Ne, accepts_encoding]
  rintro ⟨-, y, hy, hK⟩
  have hall := List.length_filter_eq_length_iff.1
    (le_antisymm (List.length_filter_le _ X) (by simpa using hK))
  have h₁ := hall [(1, 0), (0, 0)] (by simp)
  have h₂ := hall [(0, 0), (1, 0)] (by simp)
  have h₃ := hall [(0, 1), (0, 1)] (by simp)
  norm_num [intOf] at h₁ h₂ h₃
  have e₀ : y 0 = 0 := le_antisymm (by linarith) h₁
  have e₁ : y 1 = 0 := le_antisymm (by linarith) h₂
  apply hy
  funext j
  rcases j with ⟨_ | _ | j, hj⟩
  · exact e₀
  · exact e₁
  · exact absurd hj (by simp)

end MetaMathlibExt.Complexity.NPComplete.ClosedHemisphere
