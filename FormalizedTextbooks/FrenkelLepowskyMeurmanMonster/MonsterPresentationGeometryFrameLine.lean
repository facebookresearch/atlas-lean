/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual local transport realizes Conway frame points by genuine Monster residue lines. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryFrameLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryTrialityLine

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Local conjugation fixes the distinguished actual Monster geometry point. -/
theorem monsterGeometryFrame_local_base (h : H) :
    monsterGeometryPointConjugation (localIntoGenerated h) (monsterGeometryTrialityPoint 0) =
      monsterGeometryBasePoint := by
  apply Subtype.ext
  rw [monsterGeometryPointConjugation_value, monsterGeometryTrialityPoint_zero_value]
  have hc := Subgroup.mem_centralizer_singleton_iff.mp
    (localIntoGenerated_range_le_centralizer ⟨h, rfl⟩)
  change localIntoGenerated h * generatedCentralInvolution =
    generatedCentralInvolution * localIntoGenerated h at hc
  change localIntoGenerated h * generatedCentralInvolution * (localIntoGenerated h)⁻¹ =
    generatedCentralInvolution
  rw [hc, mul_inv_cancel_right]

/-- A fiber transports the actual Omega point by its literal spin automorphism. -/
theorem monsterGeometryFrame_local_omega (f : localFiberSubgroup) :
    (monsterGeometryPointConjugation (localIntoGenerated (localFiberIntoH f))
      (monsterGeometryTrialityPoint 2)).val =
        qIntoGenerated (spinConjugation f.val.1 sourceOmegaQ) := by
  have he := congrArg localIntoGenerated (inclQ_spinConjugation f sourceOmegaQ)
  simp only [map_mul, map_inv] at he
  rw [monsterGeometryPointConjugation_value]
  change localIntoGenerated (localFiberIntoH f) * centralSignIntoGenerated 2 *
    (localIntoGenerated (localFiberIntoH f))⁻¹ = _
  rw [← qIntoGenerated_sourceOmegaQ]
  exact he.symm

/-- Each local fiber gives a genuine residue line with the original six Q-incidences. -/
theorem monsterGeometryFrame_local_line (f : localFiberSubgroup) :
    monsterGeometryLine monsterGeometryBasePoint
      (monsterGeometryPointConjugation (localIntoGenerated (localFiberIntoH f))
        (monsterGeometryTrialityPoint 1))
      (monsterGeometryPointConjugation (localIntoGenerated (localFiberIntoH f))
        (monsterGeometryTrialityPoint 2)) := by
  simpa only [monsterGeometryFrame_local_base] using
    monsterGeometryLine_conjugation (localIntoGenerated (localFiberIntoH f)) _ _ _
      monsterGeometryTrialityLine

/-- Every genuine Conway point is realized by a source Omega lift on an actual line through z.
No classification of other Monster residue lines is assumed here. -/
theorem monsterGeometryFrame_line_exists (p : MonsterCo1GeometryPoint) :
    ∃ q : Q, ∃ r s : MonsterGeometryPoint,
      toAdd (qQuotHom q) = p.val ∧ qIntoGenerated q = s.val ∧
        monsterGeometryLine monsterGeometryBasePoint r s := by
  obtain ⟨f, hf⟩ := monsterGeometryFrame_reached p
  refine ⟨spinConjugation f.val.1 sourceOmegaQ,
    monsterGeometryPointConjugation (localIntoGenerated (localFiberIntoH f))
      (monsterGeometryTrialityPoint 1),
    monsterGeometryPointConjugation (localIntoGenerated (localFiberIntoH f))
      (monsterGeometryTrialityPoint 2), hf, ?_, monsterGeometryFrame_local_line f⟩
  exact (monsterGeometryFrame_local_omega f).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
