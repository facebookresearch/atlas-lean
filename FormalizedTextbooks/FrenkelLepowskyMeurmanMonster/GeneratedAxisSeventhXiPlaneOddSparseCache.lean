/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneOddSparseCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneOddPackedCertificates

/-! Exact catalogue-free middle odd evaluation using at most three original signed coefficients. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency true

/-- The exact original middle odd integer coefficient, evaluated from one compact code row. -/
def generatedSeventhXiOddSparseCache (d : Fin 2048) (i : Fin 24) : ℤ :=
  if h : generatedSeventhXiOddPackedInverse d < 232 then
    ∑ k : Fin 3,
      generatedSeventhXiOddWeights ⟨generatedSeventhXiOddPackedInverse d, h⟩ k *
        (if generatedSeventhXiOddPositions ⟨generatedSeventhXiOddPackedInverse d, h⟩ k = i.val
          then 1 else 0)
  else 0

private theorem code_rank (d : Fin 2048) (g : Fin 232)
    (hc : generatedSeventhXiOddCodes g = d.val) : generatedSeventhXiOddPackedInverse d = g.val := by
  have h := generatedSeventhXiOdd_packed_codes g
  have he : (⟨generatedSeventhXiOddCodes g, generatedSeventhXiOdd_packed_code_bound g⟩ :
      Fin 2048) = d := Fin.ext hc
  simpa only [he] using h

/-- The compact cache equals every genuine original preferred odd coefficient numerator. -/
theorem generatedSeventhXiOddSparseCache_eq (d : Fin 2048) (i : Fin 24) :
    generatedSeventhXiOddSparseCache d i = generatedSeventhXiMiddleOddNumerator d i := by
  rw [generatedSeventhXiOdd_sparse_coefficient]
  by_cases hd : generatedSeventhXiOddPackedInverse d < 232
  · let g0 : Fin 232 := ⟨generatedSeventhXiOddPackedInverse d, hd⟩
    have hc0 : generatedSeventhXiOddCodes g0 = d.val := by
      have h := generatedSeventhXiOdd_packed_inverse d
      rw [dite_eq_left hd] at h
      exact h
    have he (g : Fin 232) : generatedSeventhXiOddCodes g = d.val ↔ g = g0 := by
      constructor
      · intro hc
        apply Fin.ext
        exact (code_rank d g hc).symm
      · rintro rfl
        exact hc0
    have hrow (g : Fin 232) :
        (∑ k : Fin 3, generatedSeventhXiOddRowCoefficient d i g k) =
          if g = g0 then ∑ k : Fin 3, generatedSeventhXiOddWeights g k *
            (if generatedSeventhXiOddPositions g k = i.val then 1 else 0) else 0 := by
      by_cases hg : g = g0
      · simp only [generatedSeventhXiOddRowCoefficient, he, hg, true_and, ite_true]
      · simp only [generatedSeventhXiOddRowCoefficient, he, hg, false_and,
          ite_false, mul_zero, Finset.sum_const_zero]
    simp_rw [hrow]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true, generatedSeventhXiOddSparseCache,
      hd, dite_true, g0]
  · have hn (g : Fin 232) : generatedSeventhXiOddCodes g ≠ d.val := by
      intro hc
      have h := code_rank d g hc
      exact hd (h ▸ g.isLt)
    simp only [generatedSeventhXiOddSparseCache, hd, dite_false]
    symm
    apply Finset.sum_eq_zero
    intro g _
    apply Finset.sum_eq_zero
    intro k _
    simp only [generatedSeventhXiOddRowCoefficient, hn g, false_and, ite_false, mul_zero]

/-- The complete canonical middle odd row uses this exact small arithmetic cache. -/
theorem generatedSeventhXi_odd_sparse_coordinate (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode generatedSeventhXiPlaneCanonicalMiddle).2.1
      (Sum.inr (Sum.inr (d, i))) = (generatedSeventhXiOddSparseCache d i : ℝ) / 4 := by
  rw [generatedSeventhXi_middle_odd_arithmetic, generatedSeventhXiOddSparseCache_eq]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
