/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhTrianglePermutationGroup
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhSignParameterBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhSpatial

/-! Original Golay signs correct triangle permutations on the genuine middle norm-eight vector. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Pointwise
set_option backward.isDefEq.respectTransparency false

/-- The original residue code of the actual middle norm-eight frame vector. -/
def generatedSeventhMiddleFrameCode : golayCode := sourceGeneratedSignCode 3058

/-- Exact integral residue signs and the genuine five exceptional coordinates of that vector. -/
theorem generatedSeventh_middle_frame_sign_certificate : ∀ i : Fin 24,
    generatedSeventhFrameVectorData 7 0 i =
      (if generatedSeventhMiddleFrameCode.val i = 0 then 1 else -1) *
        (if generatedSeventhFive i then -3 else 1) := by
  decide +kernel

/-- The original residue code vanishes on all three literal triangle coordinates. -/
theorem generatedSeventh_middle_frame_code_triangle : ∀ i : Fin 24,
    generatedSeventhTriangle i → generatedSeventhMiddleFrameCode.val i = 0 := by
  decide +kernel

/-- Matrix-preserving permutations retain the genuine five-coordinate absolute-value support. -/
theorem generatedSeventh_permutation_five (p : golayAutomorphismSubgroup)
    (hp : p ∈ generatedSeventhTrianglePermutationSubgroup) (i : Fin 24) :
    generatedSeventhFive (p.val.symm i) ↔ generatedSeventhFive i := by
  have h := generatedSeventh_triangle_permutation_spatial p hp
  change conwayMatrixAction (golayPermutationIsometry p)
    (griessConwayEncode generatedSeventhAxis).1 = _ at h
  have hi := congrFun (congrFun h i) i
  rw [generatedSeventh_permutation_matrix, generatedSeventh_axis_matrix] at hi
  simp only [generatedSeventhAxisMatrix, ite_true] at hi
  change (if generatedSeventhFive (p.val.symm i) then (17 / 32 : ℝ) else 9 / 32) =
    (if generatedSeventhFive i then (17 / 32 : ℝ) else 9 / 32) at hi
  by_cases h0 : generatedSeventhFive (p.val.symm i)
  · by_cases h1 : generatedSeventhFive i
    · exact iff_of_true h0 h1
    · simp only [h0, h1, ite_true, ite_false] at hi
      norm_num at hi
  · by_cases h1 : generatedSeventhFive i
    · simp only [h0, h1, ite_true, ite_false] at hi
      norm_num at hi
    · exact iff_of_false h0 h1

/-- The correcting sign is the difference of the original and permuted genuine residue codes. -/
def generatedSeventhMiddlePermutationSign (p : golayAutomorphismSubgroup) : golayCode :=
  ⟨generatedSeventhMiddleFrameCode.val + golayPermute p.val generatedSeventhMiddleFrameCode.val,
    golayCode.add_mem generatedSeventhMiddleFrameCode.property
      ((p.property _).mp generatedSeventhMiddleFrameCode.property)⟩

/-- The actual correcting sign is admissible on the original triangle. -/
theorem generatedSeventh_middle_permutation_sign_triangle (p : golayAutomorphismSubgroup)
    (hp : p ∈ generatedSeventhTrianglePermutationSubgroup) (i : Fin 24)
    (hi : generatedSeventhTriangle i) : (generatedSeventhMiddlePermutationSign p).val i = 0 := by
  have htri := (generatedSeventh_triangle_permutation_preserves p hp).2
  have himem : i ∈ generatedSeventhTriangleCoordinates := by
    simpa only [generatedSeventhTriangleCoordinates, Finset.mem_insert,
      Finset.mem_singleton, generatedSeventhTriangle] using hi
  have hmem : p • (p.val.symm i) ∈ p • generatedSeventhTriangleCoordinates ↔
      p.val.symm i ∈ generatedSeventhTriangleCoordinates :=
    Finset.smul_mem_smul_finset_iff p
  rw [htri] at hmem
  have he : p • (p.val.symm i) = i := p.val.apply_symm_apply i
  rw [he] at hmem
  have hpi : generatedSeventhTriangle (p.val.symm i) := by
    simpa only [generatedSeventhTriangleCoordinates, Finset.mem_insert,
      Finset.mem_singleton, generatedSeventhTriangle] using hmem.mp himem
  change generatedSeventhMiddleFrameCode.val i +
    generatedSeventhMiddleFrameCode.val (p.val.symm i) = 0
  rw [generatedSeventh_middle_frame_code_triangle i hi,
    generatedSeventh_middle_frame_code_triangle _ hpi, zero_add]

/-- The corrected actual monomial isometry fixes the whole original middle norm-eight vector. -/
theorem generatedSeventh_middle_permutation_frame_fixed (p : golayAutomorphismSubgroup)
    (hp : p ∈ generatedSeventhTrianglePermutationSubgroup) :
    (golaySignIsometry (generatedSeventhMiddlePermutationSign p) * golayPermutationIsometry p).val
      (leechCoordinateEmbedding (generatedSeventhFrameVectorData 7 0)) =
        leechCoordinateEmbedding (generatedSeventhFrameVectorData 7 0) := by
  ext i
  change qSign ((generatedSeventhMiddlePermutationSign p).val i) *
    (((generatedSeventhFrameVectorData 7 0 (p.val.symm i) : ℤ) : ℝ) / Real.sqrt 8) =
      ((generatedSeventhFrameVectorData 7 0 i : ℤ) : ℝ) / Real.sqrt 8
  have hreal (j : Fin 24) : ((generatedSeventhFrameVectorData 7 0 j : ℤ) : ℝ) =
      qSign (generatedSeventhMiddleFrameCode.val j) *
        (if generatedSeventhFive j then (-3 : ℝ) else 1) := by
    rw [generatedSeventh_middle_frame_sign_certificate]
    simp only [Int.cast_mul, Int.cast_ite, Int.cast_one, Int.cast_neg, Int.cast_ofNat, qSign]
  rw [hreal, hreal]
  simp only [generatedSeventh_permutation_five p hp]
  change qSign (generatedSeventhMiddleFrameCode.val i +
    generatedSeventhMiddleFrameCode.val (p.val.symm i)) *
    ((qSign (generatedSeventhMiddleFrameCode.val (p.val.symm i)) * _) / _) = _
  rw [qSign_add, ← mul_div_assoc, ← mul_assoc, mul_assoc
    (qSign (generatedSeventhMiddleFrameCode.val i)), qSign_sq, mul_one]

/-- The genuine correcting sign has an original source label in the admissible parameter space. -/
theorem generatedSeventh_middle_permutation_sign_label (p : golayAutomorphismSubgroup)
    (hp : p ∈ generatedSeventhTrianglePermutationSubgroup) :
    ∃ d : Fin 4096, sourceGeneratedSignCode d = generatedSeventhMiddlePermutationSign p ∧
      golayLabelCoefficients d ∈ generatedSeventhSignParameterSpace := by
  obtain ⟨v, hv⟩ := (generatedSeventhMiddlePermutationSign p).property
  let d := sourceCodeLabelEquiv.symm v
  have hd : golayLabelCoefficients d = v := sourceCodeLabelEquiv.apply_symm_apply v
  have hc : sourceGeneratedSignCode d = generatedSeventhMiddlePermutationSign p := by
    apply Subtype.ext
    change golayEncoder (golayLabelCoefficients d) = _
    rw [hd, hv]
  refine ⟨d, hc, (generatedSeventhSignParameter_mem_iff _).mpr ?_⟩
  have he (i : Fin 24) : golayEncoder (golayLabelCoefficients d) i =
      (generatedSeventhMiddlePermutationSign p).val i := congrFun (congrArg Subtype.val hc) i
  rw [he 16, he 17, he 19]
  rw [generatedSeventh_middle_permutation_sign_triangle p hp 16 (Or.inl rfl),
    generatedSeventh_middle_permutation_sign_triangle p hp 17 (Or.inr (Or.inl rfl)),
    generatedSeventh_middle_permutation_sign_triangle p hp 19 (Or.inr (Or.inr rfl))]
  exact ⟨rfl, rfl⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
