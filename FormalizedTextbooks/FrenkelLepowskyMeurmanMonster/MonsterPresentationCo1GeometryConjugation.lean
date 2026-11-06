/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Genuine Conway conjugation transports actual point stabilizers and intrinsic two-cores. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometrySignCard

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every actual norm-eight frame-class point is reached from the actual base point. -/
theorem monsterCo1GeometryPoint_reached (p : MonsterCo1GeometryPoint) :
    ∃ g : Co1, g • monsterCo1GeometryBasePoint = p := by
  obtain ⟨x, ⟨e, he⟩, hx⟩ := p.property
  refine ⟨QuotientGroup.mk e, ?_⟩
  apply Subtype.ext
  change co1BinaryAction (QuotientGroup.mk e) monsterCo1GeometryBasePoint.val = p.val
  rw [monsterCo1GeometryBasePoint_value, monsterCo1GeometryClass_coordinates]
  change leechModTwoAction e (leechReduction (leechCoordinateFrameLattice 0)) = x at he
  rw [he]
  exact hx

/-- The full actual point stabilizers are canonically isomorphic under genuine Conway transport. -/
def monsterCo1GeometryStabilizerConjugation (g : Co1) (p : MonsterCo1GeometryPoint) :
    monsterCo1GeometryPointStabilizer p ≃* monsterCo1GeometryPointStabilizer (g • p) :=
  MulAction.stabilizerEquivStabilizer rfl

/-- Transport retains literal conjugation of the actual Conway group elements. -/
theorem monsterCo1GeometryStabilizerConjugation_value (g : Co1) (p : MonsterCo1GeometryPoint)
    (h : monsterCo1GeometryPointStabilizer p) :
    (monsterCo1GeometryStabilizerConjugation g p h).val = g * h.val * g⁻¹ := by
  exact MulAction.stabilizerEquivStabilizer_apply (g := g) (rfl : g • p = g • p) h

/-- The intrinsic actual point two-cores conjugate exactly under the genuine Conway action. -/
theorem monsterCo1GeometryPointTwoCore_conjugation (g : Co1) (p : MonsterCo1GeometryPoint) :
    monsterCo1GeometryPointTwoCore (g • p) =
      (monsterCo1GeometryPointTwoCore p).map (MulAut.conj g).toMonoidHom := by
  have hc := monsterGeometryTwoCore_map_equiv (monsterCo1GeometryStabilizerConjugation g p)
  unfold monsterCo1GeometryPointTwoCore
  rw [← hc, Subgroup.map_map]
  have he : (monsterCo1GeometryPointStabilizer (g • p)).subtype.comp
      (monsterCo1GeometryStabilizerConjugation g p).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp (monsterCo1GeometryPointStabilizer p).subtype := by
    ext h
    exact monsterCo1GeometryStabilizerConjugation_value g p h
  rw [he, ← Subgroup.map_map]

/-- Every actual Conway point two-core is a literal conjugate of the genuine base sign subgroup. -/
theorem monsterCo1GeometryPointTwoCore_of_reached (p : MonsterCo1GeometryPoint) (g : Co1)
    (hg : g • monsterCo1GeometryBasePoint = p) :
    monsterCo1GeometryPointTwoCore p =
      monsterCo1GeometrySignClassHom.range.map (MulAut.conj g).toMonoidHom := by
  rw [← hg, monsterCo1GeometryPointTwoCore_conjugation, monsterCo1GeometryBasePoint_twoCore]

/-- The intrinsic normal two-core of every full actual Conway point stabilizer has order 2¹¹. -/
theorem monsterCo1GeometryPointTwoCore_card (p : MonsterCo1GeometryPoint) :
    Nat.card (monsterCo1GeometryPointTwoCore p) = 2048 := by
  obtain ⟨g, hg⟩ := monsterCo1GeometryPoint_reached p
  rw [monsterCo1GeometryPointTwoCore_of_reached p g hg]
  rw [MulEquiv.toMonoidHom_eq_coe]
  rw [← Nat.card_congr ((MulAut.conj g).subgroupMap monsterCo1GeometrySignClassHom.range).toEquiv]
  exact monsterCo1GeometrySignClass_range_card

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
