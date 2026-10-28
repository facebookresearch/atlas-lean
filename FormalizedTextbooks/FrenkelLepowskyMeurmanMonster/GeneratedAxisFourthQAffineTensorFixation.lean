/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQAffineTensorFixationRows
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

private theorem fourth_scalar_fix (q : Q) (c : ℝ) (v : SpinSpace) (hc : c ≠ 0)
    (h : spinOperator q (c • v) = c • v) : spinOperator q v = v := by
  rw [map_smul] at h
  funext t
  exact mul_left_cancel₀ hc (congrFun h t)

/-- Fixing every packed-tensor column is equivalent to fixing all twenty-two affine states. -/
theorem generatedFourthQAffineTensor_fixed_iff (q : Q) :
    (∀ i : Fin 24, spinOperator q (fun t => generatedFourthQAffineTensorPacked t i) =
      (fun t => generatedFourthQAffineTensorPacked t i)) ↔
    q ∈ generatedAxisFourthQAffineFamilyStabilizer generatedAxisFourthQAffineParameterPlane
      generatedAxisFourthQAffineParameterBases generatedAxisFourthQAffineParameterCharacters := by
  constructor
  · intro h
    have hs (j : Fin 16) : spinOperator q
        (generatedAxisFourthQAffineSpinState generatedAxisFourthQAffineParameterPlane
          (generatedAxisFourthQAffineParameterBases (generatedFourthQAffineTensorFamilyIndex
            (generatedFourthQAffineTensorSingleIndices j)))
          (generatedAxisFourthQAffineParameterCharacters (generatedFourthQAffineTensorFamilyIndex
            (generatedFourthQAffineTensorSingleIndices j)))) =
        generatedAxisFourthQAffineSpinState generatedAxisFourthQAffineParameterPlane
          (generatedAxisFourthQAffineParameterBases (generatedFourthQAffineTensorFamilyIndex
            (generatedFourthQAffineTensorSingleIndices j)))
          (generatedAxisFourthQAffineParameterCharacters (generatedFourthQAffineTensorFamilyIndex
            (generatedFourthQAffineTensorSingleIndices j))) := by
      apply fourth_scalar_fix q _ _ (generatedFourthQAffineTensor_scale_ne_zero _)
      simpa only [generatedFourthQAffineTensor_packed_single] using
        h (generatedFourthQAffineTensorSingleColumns j)
    have hzero : spinOperator q
        (generatedAxisFourthQAffineSpinState generatedAxisFourthQAffineParameterPlane
          (generatedAxisFourthQAffineParameterBases 0)
          (generatedAxisFourthQAffineParameterCharacters 0)) =
        generatedAxisFourthQAffineSpinState generatedAxisFourthQAffineParameterPlane
          (generatedAxisFourthQAffineParameterBases 0)
          (generatedAxisFourthQAffineParameterCharacters 0) := hs 0
    have hu := ((generatedAxisFourthQAffineSpin_fixed_iff _ _ _ q).mp hzero).1
    have hh := h 8
    rw [generatedFourthQAffineTensor_packed_six] at hh
    have h6 := (generatedFourthQAffineSum_fixed_iff generatedAxisFourthQAffineParameterPlane
      (fun i : Fin 6 => generatedAxisFourthQAffineParameterBases
        (generatedFourthQAffineTensorFamilyIndex (generatedFourthQAffineTensorSixIndices i)))
      (fun i : Fin 6 => generatedAxisFourthQAffineParameterCharacters
        (generatedFourthQAffineTensorFamilyIndex (generatedFourthQAffineTensorSixIndices i)))
      (fun i : Fin 6 => qSign (generatedFourthQAffineTensorScalePhases
        (generatedFourthQAffineTensorSixIndices i)) / Real.sqrt 2)
      (fun i => generatedFourthQAffineTensor_scale_ne_zero _)
      generatedFourthQAffineTensor_six_disjoint
      q hu).mp hh
    intro j
    change spinOperator q (generatedAxisFourthQAffineSpinState
      generatedAxisFourthQAffineParameterPlane (generatedAxisFourthQAffineParameterBases j)
      (generatedAxisFourthQAffineParameterCharacters j)) = _
    rcases generatedFourthQAffineTensor_family_coverage j with ⟨i, hi⟩ | ⟨i, hi⟩
    · simpa only [hi] using hs i
    · simpa only [hi] using h6 i
  · intro h i
    change spinRepresentation q (fun t => generatedFourthQAffineTensorPacked t i) = _
    have he : (fun t => generatedFourthQAffineTensorPacked t i) =
        ∑ k : Fin 28,
          (qSign (generatedFourthQAffineTensorScalePhases k) / Real.sqrt 2) •
          (if i = generatedFourthQAffineTensorColumns k then
            generatedAxisFourthQAffineSpinState generatedAxisFourthQAffineParameterPlane
              (generatedAxisFourthQAffineParameterBases (generatedFourthQAffineTensorFamilyIndex k))
              (generatedAxisFourthQAffineParameterCharacters
                (generatedFourthQAffineTensorFamilyIndex k))
            else 0) := by
      funext t
      simp only [generatedFourthQAffineTensorPacked, Finset.sum_apply,
        generatedFourthQAffineTensorState, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hi : i = generatedFourthQAffineTensorColumns k <;> simp [hi]
    rw [he, map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [map_smul]
    by_cases hi : i = generatedFourthQAffineTensorColumns k
    · simp only [hi, ↓reduceIte, h (generatedFourthQAffineTensorFamilyIndex k)]
    · simp [hi]

/-- The packed-tensor stabilizer equals the declared affine-family stabilizer in Q. -/
theorem generatedFourthQAffineTensor_stabilizer_eq :
    {q : Q | ∀ i : Fin 24, spinOperator q (fun t => generatedFourthQAffineTensorPacked t i) =
      (fun t => generatedFourthQAffineTensorPacked t i)} =
    (generatedAxisFourthQAffineFamilyStabilizer generatedAxisFourthQAffineParameterPlane
      generatedAxisFourthQAffineParameterBases
      generatedAxisFourthQAffineParameterCharacters : Set Q) := by
  ext q
  exact generatedFourthQAffineTensor_fixed_iff q

/-- Exactly 128 actual elements of Q fix every spatial column of the packed original tensor. -/
theorem generatedFourthQAffineTensor_stabilizer_card :
    Nat.card {q : Q // ∀ i : Fin 24,
      spinOperator q (fun t => generatedFourthQAffineTensorPacked t i) =
        (fun t => generatedFourthQAffineTensorPacked t i)} = 128 := by
  let e : {q : Q // ∀ i : Fin 24,
      spinOperator q (fun t => generatedFourthQAffineTensorPacked t i) =
        (fun t => generatedFourthQAffineTensorPacked t i)} ≃
      generatedAxisFourthQAffineFamilyStabilizer generatedAxisFourthQAffineParameterPlane
        generatedAxisFourthQAffineParameterBases generatedAxisFourthQAffineParameterCharacters :=
    { toFun := fun q => ⟨q.val, (generatedFourthQAffineTensor_fixed_iff q.val).mp q.property⟩
      invFun := fun q => ⟨q.val, (generatedFourthQAffineTensor_fixed_iff q.val).mpr q.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  exact generatedAxisFourthQAffineParameter_stabilizer_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
