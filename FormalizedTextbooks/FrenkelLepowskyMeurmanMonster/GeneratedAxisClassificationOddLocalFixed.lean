/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddShortPairing

/-! The original odd axis is fixed by a compatible lift whose spatial line
and distinguished spin state have matching signs. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

private theorem state_zero : generatedOddSpinState 0 1 0 (0 : SpinIndex) = 1 := by
  have hz : generatedOddSpinLow (0 : SpinIndex) = 0 := rfl
  simp [generatedOddSpinState, hz]

/-- A common global spin sign cancels from all actual transported pair eigenvalues. -/
theorem generatedOddAxis_lift_pair_phase (f : localFiberSubgroup) (b : ZMod 2)
    (hspin : f.val.1.val (generatedOddSpinState 0 1 0) =
      qSign b • generatedOddSpinState 0 1 0)
    (s t : Fin 2) (p q : Fin 276)
    (hp : griessShortPermutation f.val.2 (Sum.inl (s, p)) = Sum.inl (t, q)) :
    qSign (localShortPhase f (Sum.inl (s, p))) * qSign (generatedOddPairEigenSign s) =
      qSign (generatedOddPairEigenSign t) := by
  have h := generatedOddSpin_lift_eigen f (Sum.inl (s, p))
    (generatedOddPairEigenSign s) (generatedOddSpin_pair_eigen s p)
  rw [hp, hspin, map_smul, generatedOddSpin_pair_eigen] at h
  have he := congrFun h (0 : SpinIndex)
  simp only [Pi.smul_apply, smul_eq_mul, state_zero, mul_one] at he
  have hb : qSign b ≠ 0 := by
    intro hz
    have hs := qSign_sq b
    rw [hz, zero_mul] at hs
    norm_num at hs
  rw [← qSign_add]
  apply mul_right_cancel₀ hb
  simpa only [mul_comm] using he.symm

private theorem short_zero_nonpair (r : GriessShortIndex)
    (hr : ¬ ∃ s : Fin 2, ∃ p : Fin 276, r = Sum.inl (s, p)) :
    (griessConwayEncode generatedOddAxis).2.1 r = 0 := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · exact False.elim (hr ⟨s, p, rfl⟩)
  · exact generatedAxis_triality_odd_octad_coordinate 0 0 0 o e
  · exact generatedAxis_triality_odd_odd_coordinate 0 d 0 i 0

/-- Matching spin signs and matrix fixation force every original short coordinate to be fixed. -/
theorem generatedOddAxis_lift_short_fixed (f : localFiberSubgroup)
    (hf : f.val.2 ∈ golayMonomialSubgroup) (b : ZMod 2)
    (hspin : f.val.1.val (generatedOddSpinState 0 1 0) =
      qSign b • generatedOddSpinState 0 1 0)
    (hmatrix : conwayMatrixAction f.val.2 (griessConwayEncode generatedOddAxis).1 =
      (griessConwayEncode generatedOddAxis).1) :
    localShortRepresentation f (griessConwayEncode generatedOddAxis).2.1 =
      (griessConwayEncode generatedOddAxis).2.1 := by
  classical
  ext u
  obtain ⟨r, rfl⟩ := (griessShortPermutation f.val.2).surjective u
  change localShortOperator f _ (griessShortPermutation f.val.2 r) = _
  rw [localShortOperator_image]
  by_cases hr : ∃ s : Fin 2, ∃ p : Fin 276, r = Sum.inl (s, p)
  · obtain ⟨s, p, rfl⟩ := hr
    obtain ⟨t, q, hp⟩ := generatedAxis_monomial_preserves_pair f.val.2 hf s p
    have hc := conwayShortPairing_covariant f.val.2 (griessConwayEncode generatedOddAxis).1
      (Sum.inl (s, p))
    rw [hmatrix, hp] at hc
    have hs := generatedOddAxis_lift_pair_phase f b hspin s t p q hp
    rw [hp, generatedOddAxis_short_pairing, generatedOddAxis_short_pairing, hc]
    rw [← mul_assoc, hs]
  · have hz := short_zero_nonpair r hr
    have hn : ¬ ∃ s : Fin 2, ∃ p : Fin 276,
        griessShortPermutation f.val.2 r = Sum.inl (s, p) := by
      rintro ⟨s, p, hp⟩
      obtain ⟨t, q, ht⟩ := generatedAxis_monomial_preserves_pair f.val.2⁻¹
        (golayMonomialSubgroup.inv_mem hf) s p
      rw [← hp, map_inv] at ht
      change (griessShortPermutation f.val.2).symm (griessShortPermutation f.val.2 r) = _ at ht
      rw [Equiv.symm_apply_apply] at ht
      exact hr ⟨t, q, ht⟩
    rw [hz, short_zero_nonpair _ hn, mul_zero]

/-- The genuine odd-axis tensor is the original rank-one spin-spatial tensor. -/
theorem generatedOddAxis_tensor_tmul :
    (griessConwayEncode generatedOddAxis).2.2 =
      generatedOddTensorScale • conwayTensorCoordinates
        ((generatedOddSpinState 0 1 0) ⊗ₜ[ℝ] (Pi.single (0 : Fin 24) 1)) := by
  ext t j
  rw [generatedOddAxis_tensor]
  simp only [Pi.smul_apply, smul_eq_mul, conwayTensorCoordinates_tmul, Pi.single_apply]
  ring

/-- Matching actual spatial and spin signs fix all three original coordinate blocks. -/
theorem generatedOddAxis_lift_fixed (f : localFiberSubgroup)
    (hf : f.val.2 ∈ golayMonomialSubgroup) (b : ZMod 2)
    (hspin : f.val.1.val (generatedOddSpinState 0 1 0) =
      qSign b • generatedOddSpinState 0 1 0)
    (hspatial : f.val.2.val (Pi.single (0 : Fin 24) 1) =
      qSign b • (Pi.single (0 : Fin 24) 1 : Fin 24 → ℝ))
    (hmatrix : conwayMatrixAction f.val.2 (griessConwayEncode generatedOddAxis).1 =
      (griessConwayEncode generatedOddAxis).1) :
    localGriessRepresentation f generatedOddAxis = generatedOddAxis := by
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  apply Prod.ext hmatrix
  apply Prod.ext (generatedOddAxis_lift_short_fixed f hf b hspin hmatrix)
  rw [generatedOddAxis_tensor_tmul, map_smul, localTensorRepresentation_coordinates]
  change generatedOddTensorScale • conwayTensorCoordinates
    (TensorProduct.congr f.val.1.val f.val.2.val
      ((generatedOddSpinState 0 1 0) ⊗ₜ[ℝ] (Pi.single (0 : Fin 24) 1))) = _
  rw [TensorProduct.congr_tmul, hspin, hspatial,
    TensorProduct.smul_tmul_smul, qSign_sq, one_smul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
