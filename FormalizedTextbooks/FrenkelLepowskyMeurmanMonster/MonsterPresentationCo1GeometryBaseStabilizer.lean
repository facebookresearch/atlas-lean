/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The genuine norm-eight Conway base point has the actual monomial stabilizer. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryPoints
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryMonomialTwoCore

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual distinguished Conway point is the binary class of the coordinate norm-eight frame. -/
def monsterCo1GeometryBasePoint : MonsterCo1GeometryPoint :=
  ⟨leechHyperbolicCoordinates (leechReduction (leechCoordinateFrameLattice 0)),
    leechReduction (leechCoordinateFrameLattice 0), MulAction.mem_orbit_self _, rfl⟩

/-- The literal base-point binary coordinates. -/
theorem monsterCo1GeometryBasePoint_value : monsterCo1GeometryBasePoint.val =
    leechHyperbolicCoordinates (leechReduction (leechCoordinateFrameLattice 0)) := rfl

/-- Actual Conway classes act through the genuine quotient lattice coordinate equivalence. -/
theorem monsterCo1GeometryClass_coordinates (e : leechIsomSubgroup) (x : LeechModTwo) :
    co1BinaryAction (QuotientGroup.mk e) (leechHyperbolicCoordinates x) =
      leechHyperbolicCoordinates (leechModTwoAction e x) := by
  change leechBinaryAction e (leechHyperbolicCoordinates x) = _
  simp only [leechBinaryAction, MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]

/-- The full actual Conway stabilizer is precisely the actual monomial classes. -/
theorem monsterCo1GeometryBasePoint_stabilizer :
    monsterCo1GeometryPointStabilizer monsterCo1GeometryBasePoint =
      monsterCo1GeometryMonomialClasses := by
  ext g
  induction g using QuotientGroup.induction_on with
  | H e =>
    constructor
    · intro hg
      have hv := congrArg Subtype.val hg
      change co1BinaryAction (QuotientGroup.mk e) monsterCo1GeometryBasePoint.val =
        monsterCo1GeometryBasePoint.val at hv
      rw [monsterCo1GeometryBasePoint_value, monsterCo1GeometryClass_coordinates] at hv
      have he := leechHyperbolicCoordinates.injective hv
      have hm : e ∈ golayMonomialSubgroup := by
        rw [← leechFrameClass_stabilizer_eq_monomial]
        exact he
      exact ⟨⟨e, hm⟩, rfl⟩
    · rintro ⟨h, hh⟩
      rw [← hh]
      apply Subtype.ext
      change co1BinaryAction (QuotientGroup.mk h.val) monsterCo1GeometryBasePoint.val =
        monsterCo1GeometryBasePoint.val
      rw [monsterCo1GeometryBasePoint_value, monsterCo1GeometryClass_coordinates]
      apply congrArg leechHyperbolicCoordinates
      exact leechFrameClass_stabilizer_eq_monomial.ge h.property

/-- The intrinsic actual Conway base-point two-core is exactly the genuine codeword-sign image. -/
theorem monsterCo1GeometryBasePoint_twoCore :
    monsterCo1GeometryPointTwoCore monsterCo1GeometryBasePoint =
      monsterCo1GeometrySignClassHom.range := by
  let e := MulEquiv.subgroupCongr monsterCo1GeometryBasePoint_stabilizer
  have hc := monsterGeometryTwoCore_map_equiv e.symm
  unfold monsterCo1GeometryPointTwoCore
  rw [← hc, Subgroup.map_map]
  have he : (monsterCo1GeometryPointStabilizer monsterCo1GeometryBasePoint).subtype.comp
      e.symm.toMonoidHom = monsterCo1GeometryMonomialClasses.subtype := by
    ext h
    rfl
  rw [he]
  exact monsterCo1GeometryMonomialClasses_twoCore_image

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
