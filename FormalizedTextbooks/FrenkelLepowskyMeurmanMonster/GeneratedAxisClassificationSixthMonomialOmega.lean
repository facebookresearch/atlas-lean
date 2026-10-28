/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialShortPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedForwardQLocal

/-! The four original corrected monomials commute with the signed actual source Omega element. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The full original pullbacks fix the Omega translation vector. -/
theorem generatedSixth_monomial_model_omega : ∀ k : Fin 4,
    (generatedSixthMonomialSpinModel k).coordinate *ᵥ (Pi.single 11 1 : SpinIndex) =
      Pi.single 11 1 := by
  decide +kernel

/-- No original quadratic term contains the Omega coordinate, including its diagonal term. -/
theorem generatedSixth_monomial_phase_omega_zero : ∀ k : Fin 4, ∀ i : Fin 12,
    (generatedSixthMonomialSpinModel k).phase 11 i = 0 ∧
      (generatedSixthMonomialSpinModel k).phase i 11 = 0 := by
  decide +kernel

/-- The complete original quadratic phase is invariant under Omega translation. -/
theorem generatedSixth_monomial_phase_add_omega (k : Fin 4) (t : SpinIndex) :
    monsterMonomialQuadratic (generatedSixthMonomialSpinModel k).phase
      (t + Pi.single 11 1) =
        monsterMonomialQuadratic (generatedSixthMonomialSpinModel k).phase t := by
  have hr (i : Fin 12) := (generatedSixth_monomial_phase_omega_zero k i).1
  have hc (i : Fin 12) := (generatedSixth_monomial_phase_omega_zero k i).2
  rw [monsterMonomialQuadratic_add]
  have hq : monsterMonomialQuadratic (generatedSixthMonomialSpinModel k).phase
      (Pi.single 11 1) = 0 := by
    simp [monsterMonomialQuadratic, Pi.single_apply, hr]
  have hg : spinDot (monsterMonomialGradient (generatedSixthMonomialSpinModel k).phase t)
      (Pi.single 11 1) = 0 := by
    simp [spinDot, Pi.single_apply, monsterMonomialGradient, hr, hc]
  rw [hq, hg, add_zero, add_zero]

/-- The complete original raw spin action commutes with the actual signed Omega operator. -/
theorem generatedSixth_monomial_raw_spin_omega (k : Fin 4) :
    (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.1.val * spinRepresentation sourceOmegaQ =
      spinRepresentation sourceOmegaQ *
        (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.1.val := by
  apply LinearEquiv.ext
  intro f
  funext t
  have hs : ∀ (x : SpinSpace) (u : SpinIndex),
      (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.1.val x u =
        qSign (monsterMonomialQuadratic (generatedSixthMonomialSpinModel k).phase u) *
          x ((generatedSixthMonomialSpinModel k).coordinate *ᵥ u) :=
    generatedSixth_monomial_raw_spin k
  simp only [LinearEquiv.mul_apply, sourceOmegaQ_spin]
  rw [hs, hs, sourceOmegaQ_spin]
  rw [Matrix.mulVec_add, generatedSixth_monomial_model_omega,
    generatedSixth_monomial_phase_add_omega]

/-- The raw actual spin conjugation preserves Omega with its central sign included. -/
theorem generatedSixth_monomial_raw_omega_conjugation (k : Fin 4) :
    spinConjugation (generatedSixthRawGenerator (Fin.castAdd 1 k)).val.1 sourceOmegaQ =
      sourceOmegaQ := by
  apply spinRepresentation_injective
  rw [spinConjugation_representation]
  rw [generatedSixth_monomial_raw_spin_omega]
  group

/-- The actual Q corrections have even modulation, rather than merely fixing the Omega base. -/
theorem generatedSixth_monomial_correction_even : ∀ k : Fin 4,
    spinModulation (generatedSixthGeneratorCorrection (Fin.castAdd 1 k)) 11 = 0 := by
  decide +kernel

/-- Signed spin commutation is commutation with the genuine local Omega element. -/
theorem generatedSixth_local_omega_commute (f : localFiberSubgroup)
    (hs : f.val.1.val * spinRepresentation sourceOmegaQ =
      spinRepresentation sourceOmegaQ * f.val.1.val) :
    f * localFiberIncl sourceOmegaQ = localFiberIncl sourceOmegaQ * f := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact hs
  · change f.val.2 * 1 = 1 * f.val.2
    simp

/-- Each raw original monomial commutes with the actual local Omega element. -/
theorem generatedSixth_monomial_raw_omega_commute (k : Fin 4) :
    generatedSixthRawGenerator (Fin.castAdd 1 k) * localFiberIncl sourceOmegaQ =
      localFiberIncl sourceOmegaQ * generatedSixthRawGenerator (Fin.castAdd 1 k) :=
  generatedSixth_local_omega_commute _ (generatedSixth_monomial_raw_spin_omega k)

/-- Every full corrected monomial commutes with Omega, including the preferred central phases. -/
theorem generatedSixth_monomial_corrected_omega_commute (k : Fin 4) :
    generatedSixthCorrectedGenerator (Fin.castAdd 1 k) * localFiberIncl sourceOmegaQ =
      localFiberIncl sourceOmegaQ * generatedSixthCorrectedGenerator (Fin.castAdd 1 k) := by
  have hq : localFiberIncl (generatedSixthGeneratorCorrection (Fin.castAdd 1 k)) *
      localFiberIncl sourceOmegaQ = localFiberIncl sourceOmegaQ *
        localFiberIncl (generatedSixthGeneratorCorrection (Fin.castAdd 1 k)) := by
    rw [← map_mul, ← map_mul, generatedEvenQ_commute_omega _
      (generatedSixth_monomial_correction_even k)]
  rw [generatedSixthCorrectedGenerator]
  calc
    _ = localFiberIncl (generatedSixthGeneratorCorrection (Fin.castAdd 1 k)) *
        (generatedSixthRawGenerator (Fin.castAdd 1 k) * localFiberIncl sourceOmegaQ) :=
      mul_assoc _ _ _
    _ = localFiberIncl (generatedSixthGeneratorCorrection (Fin.castAdd 1 k)) *
        (localFiberIncl sourceOmegaQ * generatedSixthRawGenerator (Fin.castAdd 1 k)) := by
      rw [generatedSixth_monomial_raw_omega_commute]
    _ = (localFiberIncl (generatedSixthGeneratorCorrection (Fin.castAdd 1 k)) *
        localFiberIncl sourceOmegaQ) * generatedSixthRawGenerator (Fin.castAdd 1 k) :=
      (mul_assoc _ _ _).symm
    _ = (localFiberIncl sourceOmegaQ *
        localFiberIncl (generatedSixthGeneratorCorrection (Fin.castAdd 1 k))) *
          generatedSixthRawGenerator (Fin.castAdd 1 k) := by rw [hq]
    _ = _ := mul_assoc _ _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
