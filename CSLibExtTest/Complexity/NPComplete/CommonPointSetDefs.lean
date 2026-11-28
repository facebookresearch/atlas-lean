/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.CommonPointSetDefs

namespace MetaMathlibExt.Complexity.NPComplete.CommonPointSet

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : CommonPointSetInstance) :
    commonPointSetDec (bitEncode i) = true ↔
      WellFormed i ∧ CommonPointSetFeasible i := by
  simp [commonPointSetDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : commonPointSetDec [true] = false := by
  have h : bitDecode (α := CommonPointSetInstance) [true] = none := rfl
  simp [commonPointSetDec, h]

open QuadraticProgramming (RatCode ratVal)

/-- The integer `n` as an encoded rational. -/
private abbrev int (n : ℕ) : RatCode := ((n, 0), 1)

private theorem point_int (n : ℕ) : point 1 [int n] = WithLp.toLp 2 fun _ => (n : ℝ) := by
  ext c
  rcases c with ⟨_ | c, hc⟩
  · simp [point, ratVal]
  · exact absurd hc (by simp)

/-- The points `0, 1` on the line, and the points `5, 6, 10`. -/
private abbrev S₁ : List (List RatCode) := [[int 0], [int 1]]
private abbrev S₂ : List (List RatCode) := [[int 5], [int 6], [int 10]]

/-- The pair `{0, 1}` is a subset of the first set and is congruent, by the translation by `5`,
to the subset `{5, 6}` of the second. -/
example : commonPointSetDec (bitEncode ((1, [S₁, S₂], 2) : CommonPointSetInstance)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, 2, le_rfl,
    fun a => point 1 [int a.val], ?_, ?_⟩
  · intro a b hab
    have := congrArg (fun p => p 0) hab
    simp only [point_int, Nat.cast_inj] at this
    exact Fin.ext this
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro S (rfl | rfl)
    · refine ⟨fun a => point 1 [int a.val], fun a => ?_, Congruent.refl _⟩
      rcases a with ⟨_ | _ | a, ha⟩
      · exact ⟨[int 0], by simp, rfl⟩
      · exact ⟨[int 1], by simp, rfl⟩
      · exact absurd ha (by simp)
    · refine ⟨(IsometryEquiv.addRight (point 1 [int 5])) ∘ fun a => point 1 [int a.val],
        fun a => ?_, Congruent.comp_right (IsometryEquiv.addRight _).isometry (Congruent.refl _)⟩
      rcases a with ⟨_ | _ | a, ha⟩
      · refine ⟨[int 5], by simp, ?_⟩
        ext c
        simp [point_int]
      · refine ⟨[int 6], by simp, ?_⟩
        ext c
        simp [point_int]
        norm_num
      · exact absurd ha (by simp)

/-- The second collection holds a single point, so no two distinct points are congruent to a
subset of it and `K = 2` is unattainable. -/
example : commonPointSetDec (bitEncode ((1, [S₁, [[int 7]]], 2) : CommonPointSetInstance)) =
    false := by
  rw [Bool.eq_false_iff, Ne, accepts_encoding]
  rintro ⟨-, m, hm, v, hv, h⟩
  obtain ⟨w, hw, hc⟩ := h [[int 7]] (by simp)
  have hm : 2 ≤ m := hm
  have hw' : ∀ a, w a = point 1 [int 7] := fun a => by
    obtain ⟨x, hx, e⟩ := hw a
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    exact hx ▸ e
  let a₀ : Fin m := ⟨0, by omega⟩
  let a₁ : Fin m := ⟨1, by omega⟩
  have e := hc a₀ a₁
  rw [hw', hw', edist_self, edist_eq_zero] at e
  exact absurd (hv e) (by simp [a₀, a₁, Fin.ext_iff])

end MetaMathlibExt.Complexity.NPComplete.CommonPointSet
