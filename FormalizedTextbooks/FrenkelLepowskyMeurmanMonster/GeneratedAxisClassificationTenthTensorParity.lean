/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthQWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthQStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalTrialityOmega
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsRawFormula

/-! The exact original Fifth tensor stabilizer detects genuine nonzero outgoing odd coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The actual original Pauli element fixing precisely the tensor's anti-Omega sector. -/
def generatedTenthTensorAntiOmega : Q := qCentralInvolution * sourceOmegaQ

/-- Excluding the genuine anti-Omega element from all32 original candidate images prevents
  fixation. -/
theorem generatedTenth_tensor_antiOmega_not_fixed_of_images (k : Fin 14)
    (hImages : ∀ b : ZMod 2, ∀ j : Fin 16,
      generatedTenthQWordImage k 7 (generatedFifthQCandidate b j) ≠
        generatedTenthTensorAntiOmega) :
    localTensorRepresentation (localFiberIncl generatedTenthTensorAntiOmega)
      (griessConwayEncode (rhoLocal (generatedAxisGlobalFifthShortLocalWord k)
        generatedFifthAxis)).2.2 ≠
      (griessConwayEncode (rhoLocal (generatedAxisGlobalFifthShortLocalWord k)
        generatedFifthAxis)).2.2 := by
  let f := generatedTenthQWordFiber k
  have hT : (griessConwayEncode (rhoLocal (generatedAxisGlobalFifthShortLocalWord k)
      generatedFifthAxis)).2.2 =
      localTensorRepresentation f (griessConwayEncode generatedFifthAxis).2.2 := by
    rw [← generatedTenth_Q_word_fiber_local]
    exact generatedFourth_local_tensor f generatedFifthAxis
  intro hfix
  rw [hT] at hfix
  obtain ⟨q, hq⟩ := (spinConjugation f.val.1).surjective generatedTenthTensorAntiOmega
  have hqT : localTensorRepresentation (localFiberIncl q)
      (griessConwayEncode generatedFifthAxis).2.2 =
      (griessConwayEncode generatedFifthAxis).2.2 := by
    apply (localTensorRepresentation f).injective
    rw [generatedAxisGlobalTensor_Q_intertwine, hq]
    exact hfix
  have hm : q ∈ generatedFifthTensorQStabilizer := by
    intro i
    funext t
    have h := congrArg (fun T : SpinIndex → Fin 24 → ℝ => T t i) hqT
    simpa only [localTensorRepresentation_q] using h
  obtain ⟨b, j, hj⟩ := (generatedFifth_tensor_Q_mem_iff q).mp hm
  apply hImages b j
  rw [hj, ← generatedTenth_Q_word_image]
  exact hq

/-- The original anti-Omega Pauli action is precisely minus the Omega shift in every tensor
  column. -/
theorem generatedTenth_tensor_antiOmega_coordinate
    (T : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation (localFiberIncl generatedTenthTensorAntiOmega) T t i =
      -T (t + Pi.single 11 1) i := by
  change localTensorRepresentation (localFiberIncl (qCentral 1 * sourceOmegaQ)) T t i = _
  rw [map_mul, map_mul, LinearEquiv.mul_apply, generatedAxisGlobalTensor_Q_central]
  simp only [Pi.smul_apply, qSign_one, smul_eq_mul, neg_one_mul]
  rw [localTensorRepresentation_q, sourceOmegaQ_spin]

/-- An input with identically zero actual odd triality output is fixed by the genuine anti-Omega
  element. -/
theorem generatedTenth_tensor_antiOmega_fixed_of_odd_zero (x : GriessSpace)
    (hOdd : ∀ d : Fin 2048, ∀ i : Fin 24,
      (griessConwayEncode (sExtra x)).2.1 (Sum.inr (Sum.inr (d, i))) = 0) :
    localTensorRepresentation (localFiberIncl generatedTenthTensorAntiOmega)
      (griessConwayEncode x).2.2 = (griessConwayEncode x).2.2 := by
  have hl (d : Fin 2048) (i : Fin 24) :
      (griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i +
        (griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i = 0 := by
    have h := hOdd d i
    rw [generatedAxisGlobalRawTrialityFormula_actual] at h
    change qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
      ((griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i +
        (griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i) /
        Real.sqrt 2 = 0 at h
    have hm := (div_eq_zero_iff.mp h).resolve_right
      (show Real.sqrt 2 ≠ 0 by positivity)
    have hs : qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) ≠ 0 := by
      intro hz
      have hh := qSign_sq (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)
      rw [hz] at hh
      norm_num at hh
    exact (mul_eq_zero.mp hm).resolve_left hs
  funext t i
  rw [generatedTenth_tensor_antiOmega_coordinate]
  obtain ⟨a, ha⟩ := golayLabelCoefficients_bijective.surjective t
  subst t
  by_cases hlow : a.val < 2048
  · let d : Fin 2048 := ⟨a.val, hlow⟩
    have h := hl d i
    change -(griessConwayEncode x).2.2
      (golayLabelCoefficients ⟨d.val, by omega⟩ + Pi.single 11 1) i =
        (griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i
    rw [golayLabel_low_add_omega]
    linear_combination -h
  · let d : Fin 2048 := ⟨a.val - 2048, by omega⟩
    have h := hl d i
    have he : (⟨d.val + 2048, by omega⟩ : Fin 4096) = a := by
      apply Fin.ext
      dsimp only [d]
      omega
    rw [he] at h
    have hs : golayLabelCoefficients a + Pi.single 11 1 =
        golayLabelCoefficients ⟨d.val, by omega⟩ := by
      have hc := congrArg golayLabelCoefficients he
      calc
        golayLabelCoefficients a + Pi.single 11 1 =
            golayLabelCoefficients ⟨d.val + 2048, by omega⟩ + Pi.single 11 1 :=
          congrArg (fun v : SpinIndex => v + Pi.single 11 1) hc.symm
        _ = (golayLabelCoefficients ⟨d.val, by omega⟩ + Pi.single 11 1) +
            Pi.single 11 1 :=
          congrArg (fun v : SpinIndex => v + Pi.single 11 1)
            (golayLabel_low_add_omega d).symm
        _ = _ := by simp only [add_assoc, ZModModule.add_self, add_zero]
    rw [hs]
    linear_combination -h

/-- The existing exact Fifth tensor classification detects an actual nonzero outgoing odd
  coordinate. -/
theorem generatedTenth_odd_nonzero_of_candidate_images (k : Fin 14)
    (hImages : ∀ b : ZMod 2, ∀ j : Fin 16,
      generatedTenthQWordImage k 7 (generatedFifthQCandidate b j) ≠
        generatedTenthTensorAntiOmega) :
    ∃ d : Fin 2048, ∃ i : Fin 24,
      (griessConwayEncode
        (sExtra (rhoLocal (generatedAxisGlobalFifthShortLocalWord k) generatedFifthAxis))).2.1
          (Sum.inr (Sum.inr (d, i))) ≠ 0 := by
  by_contra! h
  exact generatedTenth_tensor_antiOmega_not_fixed_of_images k hImages
    (generatedTenth_tensor_antiOmega_fixed_of_odd_zero _ h)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
