/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitSpatialWords

/-! Genuine full ambient actions of all fourteen monomial generators and Xi transporters. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original ten sign isometries have precisely their checked integer diagonal signs. -/
theorem sixthFrameOrbit_sign_apply (k : Fin 10) (f : Fin 24 → ℝ) (i : Fin 24) :
    (sixthFrameOrbitMonomialIsometry (Fin.castAdd 6 k)).val f i =
      (sixthFrameOrbitSpatialSign (Fin.castAdd 6 k) i : ℝ) *
        f (sixthFrameOrbitSpatialInput (Fin.castAdd 6 k) i) := by
  have hc := sixthFrameOrbit_sign_check k i
  rw [hc.2.2]
  have hk : (Fin.castAdd 6 k).val < 10 := k.isLt
  have he : sixthFrameOrbitMonomialIsometry (Fin.castAdd 6 k) =
      golaySignIsometry (sourceGeneratedSignCode (sixthFrameOrbitSignLabels k)) := by
    unfold sixthFrameOrbitMonomialIsometry
    rw [dite_eq_left hk]
    rfl
  rw [he]
  change qSign ((sourceGeneratedSignCode (sixthFrameOrbitSignLabels k)).val i) * f i = _
  have hs : qSign ((sourceGeneratedSignCode (sixthFrameOrbitSignLabels k)).val i) =
      (sixthFrameOrbitSpatialSign (Fin.castAdd 6 k) i : ℝ) := by
    by_cases hz : (sourceGeneratedSignCode (sixthFrameOrbitSignLabels k)).val i = 0
    · rw [hz, hc.1.mp hz]
      simp
    · have hsg : sixthFrameOrbitSpatialSign (Fin.castAdd 6 k) i ≠ 1 :=
        fun he => hz (hc.1.mpr he)
      have hn := hc.2.1.resolve_left hsg
      rw [hn]
      simp only [qSign, hz, ite_false, Int.cast_neg, Int.cast_one]
  exact congrArg (fun a : ℝ => a * f i) hs

/-- The six actual permutation words have exactly their original coordinate input indices. -/
theorem sixthFrameOrbit_permutation_apply (k : Fin 6) (f : Fin 24 → ℝ) (i : Fin 24) :
    (sixthFrameOrbitMonomialIsometry (Fin.natAdd 10 k)).val f i =
      f (sixthFrameOrbitSpatialInput (Fin.natAdd 10 k) i) := by
  fin_cases k
  · exact sixthFrameOrbit_raw_permutation_apply 0 f i
  · exact sixthFrameOrbit_raw_permutation_apply 1 f i
  · exact sixthFrameOrbit_raw_permutation_apply 2 f i
  · have hs : (generatedSixthRawGenerator 3).val.2 =
        golayPermutationIsometry leechRootedA2SixthPermutationWordSwap :=
      leechRootedA2GeneratingWordFiber_spatial _
    change (generatedSixthRawGenerator 3).val.2.val f i = f (sixthFrameOrbitSwapInverse i)
    rw [hs]
    change f (leechRootedA2SixthPermutationWordSwap.val.symm i) = _
    rw [sixthFrameOrbit_swap_inverse]
  · change leechRootedA2SixthXiTransportFiber.val.2.val f i = f (sixthFrameOrbitCInverse i)
    rw [leechRootedA2SixthXiTransportFiber_spatial]
    change f (leechRootedA2SixthXiTransport.val.symm i) = _
    rw [sixthFrameOrbit_C_inverse]
  · change leechRootedA2SixthXiTransportFiber.val.2⁻¹.val f i = f (sixthFrameOrbitCForward i)
    rw [leechRootedA2SixthXiTransportFiber_spatial]
    change f (leechRootedA2SixthXiTransport.val i) = _
    rw [sixthFrameOrbit_C_forward]

/-- The entire sixteen-word catalogue acts through the genuine source integer coordinate data. -/
theorem sixthFrameOrbit_monomial_apply (k : Fin 16) (f : Fin 24 → ℝ) (i : Fin 24) :
    (sixthFrameOrbitMonomialIsometry k).val f i =
      (sixthFrameOrbitSpatialSign k i : ℝ) * f (sixthFrameOrbitSpatialInput k i) := by
  by_cases hk : k.val < 10
  · have he : k = Fin.castAdd 6 (⟨k.val, hk⟩ : Fin 10) := Fin.ext rfl
    rw [he]
    exact sixthFrameOrbit_sign_apply _ f i
  · have he : k = Fin.natAdd 10 (⟨k.val - 10, by omega⟩ : Fin 6) := by
      apply Fin.ext
      simp only [Fin.val_natAdd]
      omega
    rw [he, sixthFrameOrbit_permutation_apply, sixthFrameOrbit_permutation_sign_check]
    simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
