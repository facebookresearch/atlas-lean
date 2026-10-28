/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Genuine Conway frame points have actual extraspecial lifts obtained by local conjugation. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBaseCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryConjugation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalOrbit

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- An actual Conway element admits a genuine representative in the local fiber product. -/
theorem monsterGeometryFrame_fiber_lift (g : Co1) :
    ∃ f : localFiberSubgroup, projH (localFiberIntoH f) = g := by
  obtain ⟨h, hh⟩ := projH_surjective g
  induction h using QuotientGroup.induction_on with
  | H f => exact ⟨f, hh⟩

/-- The literal source Omega quotient is the genuine Conway base-frame vector. -/
theorem monsterGeometryFrame_omega_binary :
    toAdd (qQuotHom sourceOmegaQ) = monsterCo1GeometryBasePoint.val := by
  rw [monsterCo1GeometryBasePoint_binary]
  rfl

/-- Every genuine Conway frame point is the quotient of a local conjugate of source Omega. -/
theorem monsterGeometryFrame_reached (p : MonsterCo1GeometryPoint) :
    ∃ f : localFiberSubgroup,
      toAdd (qQuotHom (spinConjugation f.val.1 sourceOmegaQ)) = p.val := by
  obtain ⟨g, hg⟩ := monsterCo1GeometryPoint_reached p
  obtain ⟨f, hf⟩ := monsterGeometryFrame_fiber_lift g
  refine ⟨f, ?_⟩
  rw [← qBinaryAction_apply]
  change spinBinaryAction f.val.1 (toAdd (qQuotHom sourceOmegaQ)) = p.val
  rw [f.property, monsterGeometryFrame_omega_binary]
  have hv := congrArg Subtype.val hg
  change co1BinaryAction g monsterCo1GeometryBasePoint.val = p.val at hv
  rw [← hf] at hv
  exact hv

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
