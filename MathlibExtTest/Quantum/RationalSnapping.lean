/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.RationalSnapping
import Mathlib.Tactic

/-!
# Tests: rational snapping
-/

@[expose] public section

namespace MathlibExtTest.Quantum.RationalSnapping

set_option autoImplicit false

open MathlibExt.Quantum.RationalSnapping

-- nonvacuity: exact rational points of the sphere are fixed (positive and negative pole signs, S^1 and S^3)
example : snap ![(3 : ℚ) / 5, 4 / 5] = ![3 / 5, 4 / 5] := by
  unfold snap
  apply stereoSnap_eq_self
  show ∑ _ : Fin 2, _ = 1
  norm_num [Fin.sum_univ_two]
example : snap ![(-3 : ℚ) / 5, -4 / 5] = ![-3 / 5, -4 / 5] := by
  unfold snap
  apply stereoSnap_eq_self
  show ∑ _ : Fin 2, _ = 1
  norm_num [Fin.sum_univ_two]
example : snap ![(1 : ℚ) / 2, 1 / 2, -1 / 2, 1 / 2] = ![1 / 2, 1 / 2, -1 / 2, 1 / 2] := by
  unfold snap
  apply stereoSnap_eq_self
  show ∑ _ : Fin 4, _ = 1
  norm_num [Fin.sum_univ_four]
-- pole rule: the largest magnitude wins even when negative; ties go to the first index
example : poleIndex ![(3 : ℚ) / 5, -4 / 5] = 1 := by
  norm_num [poleIndex, List.finRange_succ, List.finRange_zero, List.foldl_cons,
    List.foldl_nil]
example : poleIndex ![(7 : ℚ) / 10, 7 / 10] = 0 := by
  norm_num [poleIndex, List.finRange_succ, List.finRange_zero, List.foldl_cons,
    List.foldl_nil]
-- an off-sphere input lands exactly on the sphere; the output depends on the selected pole
example : snap ![(7 : ℚ) / 10, 7 / 10] = ![120 / 169, 119 / 169] := by
  have hsum : (∑ j : Fin (1 + 1),
      (if j = poleIndex ![(7 : ℚ) / 10, 7 / 10] then (0 : ℚ)
        else ![(7 : ℚ) / 10, 7 / 10] j /
          (1 + (if 0 ≤ ![(7 : ℚ) / 10, 7 / 10] (poleIndex ![(7 : ℚ) / 10, 7 / 10])
            then (1 : ℚ) else -1) *
            ![(7 : ℚ) / 10, 7 / 10] (poleIndex ![(7 : ℚ) / 10, 7 / 10])))^2) = _ :=
    Fin.sum_univ_two _
  funext j
  fin_cases j <;> simp only [snap, stereoSnap]
  · rw [hsum]
    norm_num [poleIndex, List.finRange_succ, List.finRange_zero, List.foldl_cons,
      List.foldl_nil]
  · rw [hsum]
    norm_num [poleIndex, List.finRange_succ, List.finRange_zero, List.foldl_cons,
      List.foldl_nil]
example : stereoSnap ![(7 : ℚ) / 10, 7 / 10] 1 = ![119 / 169, 120 / 169] := by
  have hsum : (∑ j : Fin (1 + 1),
      (if j = 1 then (0 : ℚ)
        else ![(7 : ℚ) / 10, 7 / 10] j /
          (1 + (if 0 ≤ ![(7 : ℚ) / 10, 7 / 10] 1 then (1 : ℚ) else -1) *
            ![(7 : ℚ) / 10, 7 / 10] 1))^2) = _ :=
    Fin.sum_univ_two _
  funext j
  fin_cases j <;> simp only [stereoSnap]
  · rw [hsum]
    norm_num
  · rw [hsum]
    norm_num
example : ∑ j, snap ![(7 : ℚ) / 10, 7 / 10] j ^ 2 = 1 := sum_sq_stereoSnap _ _

end MathlibExtTest.Quantum.RationalSnapping
