/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Both central phases over a genuine Conway frame are actual Monster geometry points. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryFrameLine

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Equal extraspecial binary coordinates differ by one of the two actual central elements. -/
theorem monsterGeometryFrame_same_binary (q k : Q)
    (h : qQuotHom q = qQuotHom k) : q = k ∨ q = qCentralInvolution * k := by
  have hd : q * k⁻¹ ∈ centerQ := by
    rw [← qQuotHom_ker]
    change qQuotHom (q * k⁻¹) = 1
    rw [map_mul, map_inv, h, mul_inv_cancel]
  by_cases he : q * k⁻¹ = 1
  · exact Or.inl (mul_inv_eq_one.mp he)
  · have hz := qCentralInvolution_eq_of_mem_center_ne_one _ hd he
    exact Or.inr (by rw [← hz]; group)

/-- The other triality point is precisely the central translate of the literal source Omega. -/
theorem monsterGeometryFrame_triality_one :
    (monsterGeometryTrialityPoint 1).val = qIntoGenerated (qCentralInvolution * sourceOmegaQ) := by
  rw [map_mul, qIntoGenerated_sourceOmegaQ]
  apply Subtype.ext
  change trialityCentralSign 1 = localCentralGriess * trialityCentralSign 2
  rw [localCentralGriess_eq_trialityCentralSign, ← trialityCentralSign_zero_mul_one,
    ← mul_assoc, trialityCentralSign_square, one_mul]

/-- A fiber transports the other phase with the same genuine spin automorphism. -/
theorem monsterGeometryFrame_local_other (f : localFiberSubgroup) :
    (monsterGeometryPointConjugation (localIntoGenerated (localFiberIntoH f))
      (monsterGeometryTrialityPoint 1)).val =
        qIntoGenerated (qCentralInvolution * spinConjugation f.val.1 sourceOmegaQ) := by
  rw [monsterGeometryPointConjugation_value, monsterGeometryFrame_triality_one]
  have he := congrArg localIntoGenerated
    (inclQ_spinConjugation f (qCentralInvolution * sourceOmegaQ))
  have he' : qIntoGenerated (spinConjugation f.val.1 (qCentralInvolution * sourceOmegaQ)) =
    localIntoGenerated (localFiberIntoH f) * qIntoGenerated (qCentralInvolution * sourceOmegaQ) *
      (localIntoGenerated (localFiberIntoH f))⁻¹ := by
    simpa only [map_mul, map_inv, qIntoGenerated, MonoidHom.comp_apply] using he
  have hz : spinConjugation f.val.1 qCentralInvolution = qCentralInvolution :=
    spinConjugation_central f.val.1 1
  rw [← he', map_mul, hz]

/-- Every extraspecial lift of an actual Conway frame vector is an actual central-involution
conjugate; the proof checks both phases through the genuine triality line. -/
theorem monsterGeometryFrame_lift_isConj (p : MonsterCo1GeometryPoint) (q : Q)
    (hq : toAdd (qQuotHom q) = p.val) :
    IsConj generatedCentralInvolution (qIntoGenerated q) := by
  obtain ⟨f, hf⟩ := monsterGeometryFrame_reached p
  have hb : qQuotHom q = qQuotHom (spinConjugation f.val.1 sourceOmegaQ) :=
    Multiplicative.toAdd.injective (hq.trans hf.symm)
  rcases monsterGeometryFrame_same_binary _ _ hb with h | h
  · rw [h, ← monsterGeometryFrame_local_omega]
    exact (monsterGeometryPointConjugation (localIntoGenerated (localFiberIntoH f))
      (monsterGeometryTrialityPoint 2)).property
  · rw [h, ← monsterGeometryFrame_local_other]
    exact (monsterGeometryPointConjugation (localIntoGenerated (localFiberIntoH f))
      (monsterGeometryTrialityPoint 1)).property

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
