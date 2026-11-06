/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Every phase over a genuine Conway frame belongs to an actual source line through z. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryFramePhases
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryLineRelations

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Central translation leaves the literal extraspecial quotient vector unchanged. -/
theorem monsterGeometryFrame_other_binary (q : Q) :
    toAdd (qQuotHom (qCentralInvolution * q)) = toAdd (qQuotHom q) := by
  change toAdd (1 * q.base) = toAdd q.base
  rw [one_mul]

/-- An arbitrary phase over an actual Conway frame defines a genuine Monster geometry point. -/
def monsterGeometryFrameLiftPoint (p : MonsterCo1GeometryPoint) (q : Q)
    (hq : toAdd (qQuotHom q) = p.val) : MonsterGeometryPoint :=
  ⟨qIntoGenerated q, monsterGeometryFrame_lift_isConj p q hq⟩

/-- Both phases form a genuine source line through the actual distinguished involution. -/
theorem monsterGeometryFrame_phase_line (p : MonsterCo1GeometryPoint) (q : Q)
    (hq : toAdd (qQuotHom q) = p.val) :
    monsterGeometryLine monsterGeometryBasePoint
      (monsterGeometryFrameLiftPoint p (qCentralInvolution * q)
        ((monsterGeometryFrame_other_binary q).trans hq))
      (monsterGeometryFrameLiftPoint p q hq) := by
  obtain ⟨f, hf⟩ := monsterGeometryFrame_reached p
  have hb : qQuotHom q = qQuotHom (spinConjugation f.val.1 sourceOmegaQ) :=
    Multiplicative.toAdd.injective (hq.trans hf.symm)
  have hz : qCentralInvolution * qCentralInvolution = 1 := by
    apply qIntoGenerated_injective
    rw [map_mul, map_one]
    exact monsterGeometryBasePoint_square
  rcases monsterGeometryFrame_same_binary _ _ hb with h | h
  · have hs : monsterGeometryFrameLiftPoint p q hq =
        monsterGeometryPointConjugation (localIntoGenerated (localFiberIntoH f))
          (monsterGeometryTrialityPoint 2) := by
      apply Subtype.ext
      change qIntoGenerated q = _
      rw [h]
      exact (monsterGeometryFrame_local_omega f).symm
    have hr : monsterGeometryFrameLiftPoint p (qCentralInvolution * q)
        ((monsterGeometryFrame_other_binary q).trans hq) =
        monsterGeometryPointConjugation (localIntoGenerated (localFiberIntoH f))
          (monsterGeometryTrialityPoint 1) := by
      apply Subtype.ext
      change qIntoGenerated (qCentralInvolution * q) = _
      rw [h]
      exact (monsterGeometryFrame_local_other f).symm
    rw [hr, hs]
    exact monsterGeometryFrame_local_line f
  · have hs : monsterGeometryFrameLiftPoint p q hq =
        monsterGeometryPointConjugation (localIntoGenerated (localFiberIntoH f))
          (monsterGeometryTrialityPoint 1) := by
      apply Subtype.ext
      change qIntoGenerated q = _
      rw [h]
      exact (monsterGeometryFrame_local_other f).symm
    have hr : monsterGeometryFrameLiftPoint p (qCentralInvolution * q)
        ((monsterGeometryFrame_other_binary q).trans hq) =
        monsterGeometryPointConjugation (localIntoGenerated (localFiberIntoH f))
          (monsterGeometryTrialityPoint 2) := by
      apply Subtype.ext
      change qIntoGenerated (qCentralInvolution * q) = _
      rw [h, ← mul_assoc, hz, one_mul]
      exact (monsterGeometryFrame_local_omega f).symm
    rw [hr, hs]
    exact monsterGeometryLine_swap_last _ _ _ (monsterGeometryFrame_local_line f)

/-- Source incidence back toward z is checked for every actual Conway-frame lift. -/
theorem monsterGeometryFrame_incident_base (p : MonsterCo1GeometryPoint) (q : Q)
    (hq : toAdd (qQuotHom q) = p.val) :
    monsterGeometryQIncident (monsterGeometryFrameLiftPoint p q hq) monsterGeometryBasePoint :=
  (monsterGeometryFrame_phase_line p q hq).2.2.2.2.2.2.2.1

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
