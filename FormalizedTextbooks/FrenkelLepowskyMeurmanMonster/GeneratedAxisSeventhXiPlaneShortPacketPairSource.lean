/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneCanonicalShort
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisSeventhXiPlaneShortPacketPackedEvaluation

/-! All three original middle pair rows and their genuine preferred-Q central phases. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The three original source pair positions, in the complete input enumeration. -/
def generatedSeventhXiShortPairPositions : Finset (Fin 276) := {211, 212, 231}

/-- The actual output pair index of each of the three original middle pair sources. -/
def generatedSeventhXiShortPairOutputIndex (p : Fin 276) : Fin 276 :=
  if p = 211 then 248 else if p = 212 then 250 else 256

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- This checks all original source descriptors, rather than assuming their physical shapes.
/-- Exactly the stated three original sources have pair outputs. -/
theorem generatedSeventhXiShort_pair_sources : ∀ s : Fin 2, ∀ p : Fin 276,
    generatedSeventhXiShortDescriptor s p 0 = 0 ↔
      s = 0 ∧ p ∈ generatedSeventhXiShortPairPositions := by
  unfold generatedSeventhXiShortPairPositions
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
-- Retain the actual two physical coordinates and both original scalar signs.
/-- Each occurring pair retains its original label, coefficient and preferred-Q phase. -/
theorem generatedSeventhXiShort_pair_source_data : ∀ p : Fin 276,
    p ∈ generatedSeventhXiShortPairPositions →
      generatedSeventhXiShortDescriptor 0 p 1 = 0 ∧
      generatedSeventhXiShortDescriptor 0 p 2 =
        (generatedSeventhXiShortInputCoordinates (generatedSeventhXiShortPairOutputIndex p)).1.val ∧
      generatedSeventhXiShortDescriptor 0 p 3 =
        (generatedSeventhXiShortInputCoordinates (generatedSeventhXiShortPairOutputIndex p)).2.val ∧
      generatedSeventhXiShortInputWeight 0 p = 1 ∧
      generatedSeventhXiShortPhaseBit 0 p = 0 := by
  unfold generatedSeventhXiShortPairPositions generatedSeventhXiShortPairOutputIndex
  decide +kernel

/-- The actual preferred catalogue output of each pair source equals its genuine input. -/
theorem generatedSeventhXiShort_pair_source_label (p : Fin 276)
    (hp : p ∈ generatedSeventhXiShortPairPositions) :
    generatedSeventhXiShortOutputLabel 0 p =
      generatedSeventhXiShortInputLabel 0 (generatedSeventhXiShortPairOutputIndex p) := by
  have hk := (generatedSeventhXiShort_pair_sources 0 p).mpr ⟨rfl, hp⟩
  obtain ⟨h1, h2, h3, _, _⟩ := generatedSeventhXiShort_pair_source_data p hp
  simp only [generatedSeventhXiShortOutputLabel, hk, dite_true,
    generatedSeventhXiShortInputLabel, generatedSeventhXiShortInputIndex]
  congr 2
  · exact Fin.ext h1
  · congr 1
    · exact Fin.ext h2
    · exact Fin.ext h3

/-- The complete original middle pair numerator contains precisely those three signed rows. -/
theorem generatedSeventhXiShort_middle_pair_sum (r : GriessShortIndex)
    (hr : ∃ s : Fin 2, ∃ p : Fin 276, r = Sum.inl (s, p)) :
    generatedSeventhXiMiddleShortNumerator r =
      ∑ p ∈ generatedSeventhXiShortPairPositions,
        (if r = generatedSeventhXiShortInputLabel 0 (generatedSeventhXiShortPairOutputIndex p)
          then (1 : ℤ) else 0) := by
  have he (s : Fin 2) (p : Fin 276) :
      generatedSeventhXiShortInputWeight s p *
        nortonUIntegerSign (generatedSeventhXiShortPhaseBit s p : ZMod 2) *
          (if r = generatedSeventhXiShortOutputLabel s p then (1 : ℤ) else 0) =
        if s = 0 ∧ p ∈ generatedSeventhXiShortPairPositions then
          (if r = generatedSeventhXiShortInputLabel 0 (generatedSeventhXiShortPairOutputIndex p)
            then 1 else 0) else 0 := by
    by_cases h : s = 0 ∧ p ∈ generatedSeventhXiShortPairPositions
    · obtain ⟨hs, hp⟩ := h
      subst s
      obtain ⟨_, _, _, hw, hc⟩ := generatedSeventhXiShort_pair_source_data p hp
      rw [generatedSeventhXiShort_pair_source_label p hp, hw, hc]
      rw [ite_eq_left (show (0 : Fin 2) = 0 ∧
        p ∈ generatedSeventhXiShortPairPositions from ⟨rfl, hp⟩)]
      simp [nortonUIntegerSign]
    · have hk := mt (generatedSeventhXiShort_pair_sources s p).mp h
      have hl : r ≠ generatedSeventhXiShortOutputLabel s p := by
        obtain ⟨a, b, rfl⟩ := hr
        by_cases h1 : generatedSeventhXiShortDescriptor s p 0 = 1 <;>
          simp [generatedSeventhXiShortOutputLabel, hk, h1]
      simp only [ite_eq_right h, ite_eq_right hl, mul_zero]
  unfold generatedSeventhXiMiddleShortNumerator
  simp_rw [he]
  rw [Fin.sum_univ_two]
  simp only [show (1 : Fin 2) ≠ 0 from by decide, false_and, true_and,
    ite_false, Finset.sum_const_zero, add_zero]
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun p => p ∈ generatedSeventhXiShortPairPositions) =
      generatedSeventhXiShortPairPositions := by simp
  rw [hf]

private theorem input_label_eq (s : Fin 2) (p q : Fin 276) :
    generatedSeventhXiShortInputLabel s p = generatedSeventhXiShortInputLabel 0 q ↔
      s = 0 ∧ p = q := by
  have hi : Function.Injective generatedSeventhXiShortInputIndex :=
    generatedSeventhXiShortInputEquiv.injective
  simp only [generatedSeventhXiShortInputLabel, Sum.inl.injEq, Prod.mk.injEq,
    hi.eq_iff]

set_option maxHeartbeats 0 in
-- The finite computation only concerns the three checked original source indices.
private theorem pair_index_sum : ∀ s : Fin 2, ∀ q : Fin 276,
    (∑ p ∈ generatedSeventhXiShortPairPositions,
      if s = 0 ∧ q = generatedSeventhXiShortPairOutputIndex p then (1 : ℤ) else 0) =
        if s = 0 ∧ (q.val = 248 ∨ q.val = 250 ∨ q.val = 256) then 1 else 0 := by
  unfold generatedSeventhXiShortPairPositions generatedSeventhXiShortPairOutputIndex
  decide +kernel

/-- The complete middle pair numerator uses the genuine output coordinates, not source indices. -/
theorem generatedSeventhXiShort_middle_pair_input (s : Fin 2) (p : Fin 276) :
    generatedSeventhXiMiddleShortNumerator (generatedSeventhXiShortInputLabel s p) =
      if s = 0 ∧ (p.val = 248 ∨ p.val = 250 ∨ p.val = 256) then 1 else 0 := by
  rw [generatedSeventhXiShort_middle_pair_sum (generatedSeventhXiShortInputLabel s p)
    ⟨s, generatedSeventhXiShortInputIndex p, rfl⟩]
  simp_rw [input_label_eq]
  exact pair_index_sum s p

set_option maxHeartbeats 0 in
-- Bind the already checked physical frame convention at every actual coordinate.
/-- The packed tensor frame is the same genuine norm-eight numerator as the canonical matrix. -/
theorem generatedSeventhXiShort_frame_actual : ∀ i : Fin 24,
    generatedSeventhNormEightVectorData 7 i = generatedSeventhXiTensorFrame i := by
  decide +kernel

/-- Every canonical pair coefficient has the complete signed packet numerator. -/
theorem generatedSeventhXiShort_pair_coefficient (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.1
      (generatedSeventhXiShortInputLabel s p) =
      ((if p.val = 248 ∨ p.val = 250 ∨ p.val = 256 then (4 : ℤ) else 0) +
        (if s = 0 then 1 else -1) *
          generatedSeventhXiTensorFrame (generatedSeventhXiShortInputCoordinates p).1 *
          generatedSeventhXiTensorFrame (generatedSeventhXiShortInputCoordinates p).2 : ℤ) /
        32 := by
  change (griessConwayEncode generatedSeventhXiPlaneCanonicalAxis).2.1
    (Sum.inl (s, generatedSeventhXiShortInputIndex p)) = _
  rw [generatedSeventhXi_canonical_axis_pair, generatedSeventhXiShortInputIndex_coordinates]
  change (4 * ((generatedSeventhXiMiddleShortNumerator
      (generatedSeventhXiShortInputLabel 0 p) : ℝ) -
      (generatedSeventhXiMiddleShortNumerator (generatedSeventhXiShortInputLabel 1 p) : ℝ)) +
    (if s = 0 then 1 else -1) *
      (generatedSeventhNormEightVectorData 7 (generatedSeventhXiShortInputCoordinates p).1 : ℝ) *
      (generatedSeventhNormEightVectorData 7 (generatedSeventhXiShortInputCoordinates p).2 : ℝ)) /
    32 = _
  rw [generatedSeventhXiShort_middle_pair_input, generatedSeventhXiShort_middle_pair_input,
    generatedSeventhXiShort_frame_actual, generatedSeventhXiShort_frame_actual]
  simp only [show (1 : Fin 2) ≠ 0 from by decide, false_and, true_and, ite_false]
  split_ifs <;> push_cast <;> ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
