/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The genuine triality Klein four supplies an actual line of the source geometry. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalTrialityOmega

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Each checked triality sign is a genuine point in the actual central-involution orbit. -/
noncomputable def monsterGeometryTrialityPoint (k : Fin 3) : MonsterGeometryPoint :=
  ⟨generatedCentralSign k, (monsterGeometryPoint_mem_iff_orbit _).mpr
    (generatedCentralSign_mem_orbit k)⟩

/-- Distinct triality signs give distinct actual geometry points. -/
theorem monsterGeometryTrialityPoint_injective :
    Function.Injective monsterGeometryTrialityPoint := by
  intro k l h
  exact generatedCentralSign_injective (congrArg Subtype.val h)

/-- The first triality sign is literally the distinguished actual involution. -/
theorem monsterGeometryTrialityPoint_zero_value :
    (monsterGeometryTrialityPoint 0).val = generatedCentralInvolution := by
  apply Subtype.ext
  exact localCentralGriess_eq_trialityCentralSign.symm

/-- All three triality signs belong to the distinguished actual extraspecial subgroup. -/
theorem monsterGeometryTrialityPoint_Q (k : Fin 3) :
    (monsterGeometryTrialityPoint k).val ∈ qIntoGenerated.range := by
  fin_cases k
  · change (monsterGeometryTrialityPoint 0).val ∈ qIntoGenerated.range
    rw [monsterGeometryTrialityPoint_zero_value]
    exact ⟨qCentralInvolution, rfl⟩
  · refine ⟨qCentralInvolution * sourceOmegaQ, ?_⟩
    rw [map_mul, qIntoGenerated_sourceOmegaQ]
    apply Subtype.ext
    change localCentralGriess * trialityCentralSign 2 = trialityCentralSign 1
    rw [localCentralGriess_eq_trialityCentralSign, ← trialityCentralSign_zero_mul_one,
      ← mul_assoc, trialityCentralSign_square, one_mul]
  · exact ⟨sourceOmegaQ, qIntoGenerated_sourceOmegaQ⟩

/-- Actual triality conjugation permutes the three literal geometry points cyclically. -/
theorem monsterGeometryTrialityPoint_conjugation (k : Fin 3) :
    monsterGeometryPointConjugation extraIntoGenerated (monsterGeometryTrialityPoint k) =
      monsterGeometryTrialityPoint (trialityCycle k) := by
  apply Subtype.ext
  apply Subtype.ext
  exact trialityCentralSign_conjugate k

/-- The base point is Q-incident to both other literal triality points. -/
theorem monsterGeometryTrialityPoint_base_QIncident (k : Fin 3) :
    monsterGeometryQIncident (monsterGeometryTrialityPoint 0) (monsterGeometryTrialityPoint k) := by
  obtain ⟨x, hx⟩ := monsterGeometryTrialityPoint_Q k
  refine ⟨1, ?_, x, ?_⟩
  · simpa only [one_mul, inv_one, mul_one] using
      monsterGeometryTrialityPoint_zero_value.symm
  · simpa only [one_mul, inv_one, mul_one] using hx

/-- Transporting actual incidence by triality retains the exact source Q-membership predicate. -/
theorem monsterGeometryTrialityPoint_QIncident_cycle (k l : Fin 3)
    (h : monsterGeometryQIncident (monsterGeometryTrialityPoint k)
      (monsterGeometryTrialityPoint l)) :
    monsterGeometryQIncident (monsterGeometryTrialityPoint (trialityCycle k))
      (monsterGeometryTrialityPoint (trialityCycle l)) := by
  simpa only [monsterGeometryTrialityPoint_conjugation] using
    monsterGeometryQIncident_conjugation extraIntoGenerated _ _ h

/-- The three genuine triality signs constitute an actual source geometry line. -/
theorem monsterGeometryTrialityLine :
    monsterGeometryLine (monsterGeometryTrialityPoint 0) (monsterGeometryTrialityPoint 1)
      (monsterGeometryTrialityPoint 2) := by
  have c0 : trialityCycle 0 = 1 := by decide +kernel
  have c1 : trialityCycle 1 = 2 := by decide +kernel
  have c2 : trialityCycle 2 = 0 := by decide +kernel
  have h01 := monsterGeometryTrialityPoint_base_QIncident 1
  have h02 := monsterGeometryTrialityPoint_base_QIncident 2
  have h12 := monsterGeometryTrialityPoint_QIncident_cycle 0 1 h01
  have h10 := monsterGeometryTrialityPoint_QIncident_cycle 0 2 h02
  have h20 := monsterGeometryTrialityPoint_QIncident_cycle 1 2 h12
  have h21 := monsterGeometryTrialityPoint_QIncident_cycle 1 0 h10
  simp only [c0, c1, c2] at h12 h10 h20 h21
  refine ⟨monsterGeometryTrialityPoint_injective.ne (by decide),
    monsterGeometryTrialityPoint_injective.ne (by decide),
    monsterGeometryTrialityPoint_injective.ne (by decide), ?_, h01, h10, h02, h20, h12, h21⟩
  apply Subtype.ext
  change trialityCentralSign 0 * trialityCentralSign 1 * trialityCentralSign 2 = 1
  rw [trialityCentralSign_zero_mul_one, trialityCentralSign_square]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
