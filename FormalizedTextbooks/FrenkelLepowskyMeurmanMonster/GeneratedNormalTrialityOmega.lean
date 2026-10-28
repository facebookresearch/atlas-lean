/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual source Ω element and its genuine triality fusion with the central sign. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOddCocode
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOddSpinPair

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The source all-one code element in the modified hyperbolic frame. -/
def sourceOmegaQ : Q := ⟨ofAdd (Pi.single (Fin.castAdd 12 (11 : Fin 12)) 1), 1⟩

@[simp] theorem sourceOmegaQ_translation : spinTranslation sourceOmegaQ = Pi.single 11 1 := by
  funext k
  simp [spinTranslation, sourceOmegaQ, Pi.single_apply, Fin.ext_iff]

@[simp] theorem sourceOmegaQ_modulation : spinModulation sourceOmegaQ = 0 := by
  funext k
  have hn : Fin.natAdd 12 k ≠ Fin.castAdd 12 (11 : Fin 12) := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
    omega
  change (Pi.single (Fin.castAdd 12 (11 : Fin 12)) 1 : Fin 24 → ZMod 2) (Fin.natAdd 12 k) = 0
  simp only [Pi.single_apply, ite_eq_right hn]

/-- Ω translates coefficient eleven in the actual Schrödinger model. -/
theorem sourceOmegaQ_spin (x : SpinSpace) (t : SpinIndex) :
    spinRepresentation sourceOmegaQ x t = x (t + Pi.single 11 1) := by
  change qSign (spinPhase sourceOmegaQ t) * x (t + spinTranslation sourceOmegaQ) = _
  rw [spinPhase, sourceOmegaQ_translation, sourceOmegaQ_modulation]
  change qSign (0 + spinDot 0 t) * x (t + Pi.single 11 1) = _
  simp [spinDot]

/-- Ω's genuine conjugation phase is the last cocode coordinate. -/
theorem sourceOmegaQ_short_phase (r : GriessShortIndex) :
    localShortPhase (localFiberIncl sourceOmegaQ) r = spinModulation (griessShortQ r) 11 := by
  change toAdd (spinConjugation (spinHolomorphIncl sourceOmegaQ) (griessShortQ r)).coeff = _
  rw [spinConjugation_incl, q_conjugation_central_phase, qCentral_mul_coeff,
    griessShortQ_coeff, add_zero]
  rw [qBeta_spin_coordinates, qBeta_spin_coordinates,
    sourceOmegaQ_translation, sourceOmegaQ_modulation]
  simp [spinDot, Pi.single_apply]

theorem sourceOmegaQ_short (x : GriessShortIndex → ℝ) (r : GriessShortIndex) :
    localShortRepresentation (localFiberIncl sourceOmegaQ) x r =
      qSign (spinModulation (griessShortQ r) 11) * x r := by
  have hp : griessShortPermutation (localFiberIncl sourceOmegaQ).val.2 r = r := by
    change griessShortPermutation 1 r = r
    rw [map_one]; rfl
  have he := localShortOperator_image (localFiberIncl sourceOmegaQ) x r
  rw [hp, sourceOmegaQ_short_phase] at he
  exact he

/-- Ω fixes pair and octad short coordinates and negates the odd short family. -/
theorem sourceOmegaQ_short_family (x : GriessShortIndex → ℝ) :
    localShortRepresentation (localFiberIncl sourceOmegaQ) x = fun r =>
      match r with
      | Sum.inl _ => x r
      | Sum.inr (Sum.inl _) => x r
      | Sum.inr (Sum.inr _) => -x r := by
  funext r
  rw [sourceOmegaQ_short]
  rcases r with ⟨s,p⟩ | (⟨o,e⟩ | ⟨d,i⟩)
  · rw [griessPairQ_modulation, griessPairSyndrome_omega, qSign_zero, one_mul]
  · rw [griessOctad_modulation_last, qSign_zero, one_mul]
  · rw [griessOdd_modulation_last, qSign_one, neg_one_mul]

/-- The actual Ω operator translates the spin column in the physical tensor dictionary. -/
theorem sourceOmegaQ_tensor (x : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) :
    localTensorRepresentation (localFiberIncl sourceOmegaQ) x t i =
      x (t + Pi.single 11 1) i := by
  rw [localTensorRepresentation_q, sourceOmegaQ_spin]

/-- Translating coefficient eleven keeps the lower code dictionary label. -/
theorem spinDictionaryCode_add_last (t : SpinIndex) :
    spinDictionaryCode (t + Pi.single 11 1) = spinDictionaryCode t := by
  simpa [trialitySpinOmega] using spinDictionaryCode_add_omega_smul t (1 : ZMod 2)

/-- The physical encoding of Ω is exactly the Z-positive central sign operation. -/
theorem sourceOmegaQ_encode (x : GriessSpace) :
    griessConwayEncode (rhoLocal (inclQ sourceOmegaQ) x) =
      griessConwayEncode (trialityCentralSign 2 x) := by
  rw [show rhoLocal (inclQ sourceOmegaQ) = localGriessRepresentation
      (localFiberIncl sourceOmegaQ) from rfl, localGriessRepresentation_encode,
    localConwayRawRepresentation_apply, sourceOmegaQ_short_family]
  change (conwayMatrixAction 1 (griessConwayEncode x).1, _) = _
  rw [map_one]
  apply Prod.ext
  · simp only [griessConwayEncode, trialityCentralSign_blocks,
      trialityCentralBlockAction_apply]
    rfl
  · apply Prod.ext
    · funext r
      rcases r with ⟨s,p⟩ | (⟨o,e⟩ | ⟨d,i⟩)
      · simp only [griessConwayEncode, trialityCentralSign_blocks,
          trialityCentralBlockAction_apply]
      · simp only [griessConwayEncode, trialityCentralSign_blocks,
          trialityCentralBlockAction_apply]
      · simp only [griessConwayEncode, trialityCentralSign_blocks,
          trialityCentralBlockAction_apply, show (0 : Fin 3) ≠ 2 by decide,
          ite_false, neg_one_mul]
    · funext t i
      change localTensorRepresentation (localFiberIncl sourceOmegaQ)
        (griessConwayEncode x).2.2 t i = (griessConwayEncode (trialityCentralSign 2 x)).2.2 t i
      rw [sourceOmegaQ_tensor]
      simp only [griessConwayEncode, trialityCentralSign_blocks,
        trialityCentralBlockAction_apply, spinDictionaryCode_add_last,
        Pi.add_apply, Pi.single_eq_same, qSign_add, qSign_one, mul_neg_one,
        show (1 : Fin 3) ≠ 2 by decide, ite_false, ite_true, one_mul, neg_one_mul]
      ring

/-- The genuine local Ω element equals a genuine triality conjugate of the central involution. -/
theorem sourceOmegaQ_eq_trialityCentralSign :
    rhoLocal (inclQ sourceOmegaQ) = trialityCentralSign 2 := by
  apply LinearEquiv.ext
  intro x
  have h := congrArg griessConwayDecode (sourceOmegaQ_encode x)
  simpa only [griessConwayDecode_encode] using h

/-- This fused central sign genuinely belongs to the embedded extraspecial group. -/
theorem centralSign_two_mem_q_range : centralSignIntoGenerated 2 ∈ qIntoGenerated.range := by
  refine ⟨sourceOmegaQ, ?_⟩
  apply Subtype.ext
  exact sourceOmegaQ_eq_trialityCentralSign

/-- The source Ω element is outside the extraspecial center. -/
theorem sourceOmegaQ_not_mem_center : sourceOmegaQ ∉ centerQ := by
  intro hz
  have he := (q_mem_center_iff_base_eq_one sourceOmegaQ).mp hz
  have hk := congrArg (fun b : Multiplicative (Fin 24 → ZMod 2) =>
    toAdd b (Fin.castAdd 12 (11 : Fin 12))) he
  apply (one_ne_zero : (1 : ZMod 2) ≠ 0)
  simpa only [sourceOmegaQ, toAdd_ofAdd, toAdd_one, Pi.zero_apply, Pi.single_eq_same] using hk

/-- Equality in the actual generated group, before using any normal-subgroup argument. -/
theorem qIntoGenerated_sourceOmegaQ :
    qIntoGenerated sourceOmegaQ = centralSignIntoGenerated 2 := by
  apply Subtype.ext
  exact sourceOmegaQ_eq_trialityCentralSign

/-- A normal subgroup containing the genuine central involution also contains the noncentral Ω. -/
theorem sourceOmegaQ_mem_of_generatedCentral_mem (N : Subgroup ↥G) [N.Normal]
    (hz : qIntoGenerated qCentralInvolution ∈ N) : qIntoGenerated sourceOmegaQ ∈ N := by
  rw [qIntoGenerated_sourceOmegaQ]
  exact centralSigns_mem_of_generatedCentral_mem N hz 2

/-- The Q intersection of such a normal subgroup extends strictly beyond the center. -/
theorem q_intersection_not_le_center_of_generatedCentral_mem (N : Subgroup ↥G) [N.Normal]
    (hz : qIntoGenerated qCentralInvolution ∈ N) : ¬ N.comap qIntoGenerated ≤ centerQ := by
  intro h
  exact sourceOmegaQ_not_mem_center (h (sourceOmegaQ_mem_of_generatedCentral_mem N hz))

/-- Nontrivial local intersection forces the Q intersection strictly beyond its center. -/
theorem q_intersection_not_le_center_of_nontrivial_local_intersection
    (N : Subgroup ↥G) [N.Normal] (hN : N.comap localIntoGenerated ≠ ⊥) :
    ¬ N.comap qIntoGenerated ≤ centerQ :=
  q_intersection_not_le_center_of_generatedCentral_mem N
    (generatedCentral_mem_of_nontrivial_local_intersection N hN)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
