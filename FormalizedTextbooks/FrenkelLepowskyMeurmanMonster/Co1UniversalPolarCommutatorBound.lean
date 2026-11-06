/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1GeometryPolarGraphConnected
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1UniversalPresentationLineCommutation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryLineBinary
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1GeometryCommutatorBound

/-! A concrete alternative polar-graph route to the actual universal commutator bound.
The two remaining geometric inputs are explicit hypotheses, not established here. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Connectivity through genuine lines within every actual polar-neighbor set. -/
def monsterCo1PolarLocalConnected : Prop :=
  ∀ x : MonsterCo1GeometryPoint,
    ∀ u v : {y : MonsterCo1GeometryPoint // monsterCo1GeometryPolarAdjacent x y},
      Relation.ReflTransGen
        (fun u v : {y : MonsterCo1GeometryPoint // monsterCo1GeometryPolarAdjacent x y} =>
          monsterCo1GeometryAdjacent u.val v.val) u v

/-- A genuine line through two polar neighbors has its third point polar-orthogonal to the base. -/
theorem monsterCo1PolarLocal_line_third (x p q r : MonsterCo1GeometryPoint)
    (hp : monsterCo1GeometryPolarAdjacent x p) (hq : monsterCo1GeometryPolarAdjacent x q)
    (hline : monsterCo1GeometryLine p q r) : ¬ monsterCo1GeometryPolarAdjacent x r := by
  have h := congrArg (co1BinaryPolar x.val) (monsterCo1GeometryLine_binary p q r hline)
  rw [map_add, map_add, map_zero, show co1BinaryPolar x.val p.val = 1 from hp,
    show co1BinaryPolar x.val q.val = 1 from hq] at h
  have htwo : (1 : ZMod 2) + 1 = 0 := by decide +kernel
  rw [htwo, zero_add] at h
  have hz : co1BinaryPolar x.val r.val = 0 := h
  change co1BinaryPolar x.val r.val ≠ 1
  rw [hz]
  exact zero_ne_one

/-- Actual polar geometry supplies all generic commutator graph data once
local connectivity holds. -/
def co1UniversalPolarGeometry (hlocal : monsterCo1PolarLocalConnected) :
    Co1GeometryCommutatorGeometry MonsterCo1GeometryPoint where
  distant := monsterCo1GeometryPolarAdjacent
  line := monsterCo1GeometryLine
  distant_symm := monsterCo1PolarGraph_symm
  connected := monsterCo1Geometry_polar_connected
  line_distinct := by
    intro p q r h
    rcases h with hp | hq | hr
    · exact ⟨hp.1, hp.2.2.1, hp.2.1.symm⟩
    · exact ⟨hq.1.symm, hq.2.1, hq.2.2.1.symm⟩
    · exact ⟨hr.2.2.1, hr.2.1.symm, hr.1⟩
  line_exists := by
    obtain ⟨r, hr, _⟩ := monsterCo1GeometryTetradLine_exists
    exact ⟨monsterCo1GeometryBasePoint, monsterCo1GeometryTetradPoint, r, Or.inl hr⟩
  local_connected := by
    intro x u v
    apply Relation.ReflTransGen.mono (r :=
      fun a b : {y : MonsterCo1GeometryPoint // monsterCo1GeometryPolarAdjacent x y} =>
        monsterCo1GeometryAdjacent a.val b.val) ?_ u v (hlocal x u v)
    intro a b h
    obtain ⟨r, hr⟩ := h
    exact ⟨r, Or.inl hr, monsterCo1PolarLocal_line_third x a.val b.val r
      a.property b.property hr⟩

/-- The independent original source group supplies the generic representation with explicit
polar-orthogonal commutation as the remaining group-theoretic hypothesis. -/
def co1UniversalPolarRepresentation (hlocal : monsterCo1PolarLocalConnected)
    (hclose : ∀ p q : MonsterCo1GeometryPoint, ¬ monsterCo1GeometryPolarAdjacent p q →
      Commute (PresentedGroup.of p : Co1UniversalPresentation) (PresentedGroup.of q)) :
    Co1GeometryCommutatorRepresentation (co1UniversalPolarGeometry hlocal)
      Co1UniversalPresentation where
  point := PresentedGroup.of
  square := co1UniversalPoint_mul_self
  line_product := co1UniversalPoint_line
  close_commute := hclose
  generates := co1UniversalPoint_generates

/-- With the two explicit remaining actual inputs, the source commutator is central. -/
theorem co1Universal_commutator_central_of_polar_geometry
    (hlocal : monsterCo1PolarLocalConnected)
    (hclose : ∀ p q : MonsterCo1GeometryPoint, ¬ monsterCo1GeometryPolarAdjacent p q →
      Commute (PresentedGroup.of p : Co1UniversalPresentation) (PresentedGroup.of q)) :
    commutator Co1UniversalPresentation ≤ Subgroup.center Co1UniversalPresentation :=
  co1GeometryCommutator_le_center (co1UniversalPolarGeometry hlocal)
    (co1UniversalPolarRepresentation hlocal hclose)

/-- The two explicit actual geometric inputs imply the required finite commutator bound. -/
theorem co1Universal_commutator_card_le_two_of_polar_geometry
    (hlocal : monsterCo1PolarLocalConnected)
    (hclose : ∀ p q : MonsterCo1GeometryPoint, ¬ monsterCo1GeometryPolarAdjacent p q →
      Commute (PresentedGroup.of p : Co1UniversalPresentation) (PresentedGroup.of q)) :
    Finite (commutator Co1UniversalPresentation) ∧
      Nat.card (commutator Co1UniversalPresentation) ≤ 2 :=
  co1GeometryCommutator_finite_card_le_two (co1UniversalPolarGeometry hlocal)
    (co1UniversalPolarRepresentation hlocal hclose)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
