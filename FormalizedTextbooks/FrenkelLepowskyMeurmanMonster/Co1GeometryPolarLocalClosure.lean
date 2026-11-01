/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1GeometryPolarLocalConnected
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1UniversalPresentationAction

/-! Genuine-line closure isolates the remaining polar-orthogonal commutation obligation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The closure of the base and its original collinear points under original genuine lines. -/
inductive monsterCo1PolarLocalLineClosure (p : MonsterCo1GeometryPoint) :
    MonsterCo1GeometryPoint → Prop
  | base : monsterCo1PolarLocalLineClosure p p
  | adjacent {q} : monsterCo1GeometryAdjacent p q → monsterCo1PolarLocalLineClosure p q
  | line {q r s} : monsterCo1GeometryLine q r s →
      monsterCo1PolarLocalLineClosure p q → monsterCo1PolarLocalLineClosure p r →
        monsterCo1PolarLocalLineClosure p s

/-- Genuine-line closure is equivariant under the actual source Co1 action. -/
theorem monsterCo1PolarLocalLineClosure_smul (g : Co1) {p q : MonsterCo1GeometryPoint}
    (h : monsterCo1PolarLocalLineClosure p q) :
    monsterCo1PolarLocalLineClosure (g • p) (g • q) := by
  induction h with
  | base => exact .base
  | adjacent h => exact .adjacent (monsterCo1GeometryAdjacent_smul g _ _ h)
  | line h _ _ ihq ihr =>
    exact .line (monsterCo1GeometryLine_smul g _ _ _ h) ihq ihr

/-- Source relations identify the third point of a genuine line as the inverse product. -/
theorem monsterCo1PolarLocalLineClosure_point_product (q r s : MonsterCo1GeometryPoint)
    (h : monsterCo1GeometryLine q r s) :
    (PresentedGroup.of s : Co1UniversalPresentation) =
      ((PresentedGroup.of q : Co1UniversalPresentation) * PresentedGroup.of r)⁻¹ := by
  have hprod := co1UniversalPoint_line q r s h
  exact eq_inv_of_mul_eq_one_right hprod

/-- Every point in the genuine-line closure commutes with its original source base generator. -/
theorem monsterCo1PolarLocalLineClosure_commute {p q : MonsterCo1GeometryPoint}
    (h : monsterCo1PolarLocalLineClosure p q) :
    Commute (PresentedGroup.of p : Co1UniversalPresentation) (PresentedGroup.of q) := by
  induction h with
  | base => exact Commute.refl _
  | adjacent h => exact co1UniversalPoint_commute_of_adjacent _ _ h
  | line h _ _ ihq ihr =>
    rw [monsterCo1PolarLocalLineClosure_point_product _ _ _ h]
    exact (ihq.mul_right ihr).inv_right

/-- The sole remaining coverage condition for the genuine-line closure at the actual base. -/
def monsterCo1PolarLocalLineClosureCoversBase : Prop :=
  ∀ q : MonsterCo1GeometryPoint,
    ¬ monsterCo1GeometryPolarAdjacent monsterCo1GeometryBasePoint q →
      monsterCo1PolarLocalLineClosure monsterCo1GeometryBasePoint q

/-- Every actual polar-orthogonal point has an even norm-eight physical representative. -/
theorem monsterCo1PolarLocal_orthogonal_representative (q : MonsterCo1GeometryPoint)
    (hq : ¬ monsterCo1GeometryPolarAdjacent monsterCo1GeometryBasePoint q) :
    ∃ u : leechIntegral, leechSquareSum u.val = 64 ∧
      leechHyperbolicCoordinates (leechReduction u) = q.val ∧
      ∀ i : Fin 24, (u.val i : ZMod 2) = 0 := by
  obtain ⟨u, hn, hu⟩ := monsterCo1PolarLocal_point_representative q
  refine ⟨u, hn, hu, ?_⟩
  intro i
  have hz : co1BinaryPolar monsterCo1GeometryBasePoint.val q.val = 0 := by
    have hbits : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide +kernel
    exact (hbits _).resolve_right hq
  rw [← monsterCo1PolarLocal_base_pairing u i, hu, hz]

/-- It suffices to prove genuine-line closure for the six even norm-eight source shapes. -/
theorem monsterCo1PolarLocalLineClosure_covers_of_even_representatives
    (h : ∀ (u : leechIntegral), leechSquareSum u.val = 64 →
      (∀ i : Fin 24, (u.val i : ZMod 2) = 0) →
      ∀ q : MonsterCo1GeometryPoint,
        leechHyperbolicCoordinates (leechReduction u) = q.val →
          monsterCo1PolarLocalLineClosure monsterCo1GeometryBasePoint q) :
    monsterCo1PolarLocalLineClosureCoversBase := by
  intro q hq
  obtain ⟨u, hn, hu, he⟩ := monsterCo1PolarLocal_orthogonal_representative q hq
  exact h u hn he q hu

/-- Actual point transitivity transports genuine-line closure coverage to every base point. -/
theorem monsterCo1PolarLocalLineClosure_covers_all
    (hcover : monsterCo1PolarLocalLineClosureCoversBase) (p q : MonsterCo1GeometryPoint)
    (hpq : ¬ monsterCo1GeometryPolarAdjacent p q) : monsterCo1PolarLocalLineClosure p q := by
  obtain ⟨g, hg⟩ := monsterCo1GeometryPoint_reached p
  have hzero : ¬ monsterCo1GeometryPolarAdjacent monsterCo1GeometryBasePoint (g⁻¹ • q) := by
    intro h
    have ht := monsterCo1PolarGraph_smul g _ _ h
    rw [hg, smul_inv_smul] at ht
    exact hpq ht
  have h := monsterCo1PolarLocalLineClosure_smul g (hcover _ hzero)
  simpa only [hg, smul_inv_smul] using h

/-- Genuine-line closure coverage proves polar-orthogonal commutation in the source group. -/
theorem monsterCo1PolarLocal_commute_of_line_closure
    (hcover : monsterCo1PolarLocalLineClosureCoversBase) (p q : MonsterCo1GeometryPoint)
    (hpq : ¬ monsterCo1GeometryPolarAdjacent p q) :
    Commute (PresentedGroup.of p : Co1UniversalPresentation) (PresentedGroup.of q) :=
  monsterCo1PolarLocalLineClosure_commute
    (monsterCo1PolarLocalLineClosure_covers_all hcover p q hpq)

/-- With genuine-line coverage, the unconditional local paths give the source commutator bound. -/
theorem monsterCo1PolarLocal_commutator_bound_of_line_closure
    (hcover : monsterCo1PolarLocalLineClosureCoversBase) :
    Finite (commutator Co1UniversalPresentation) ∧
      Nat.card (commutator Co1UniversalPresentation) ≤ 2 :=
  co1Universal_commutator_card_le_two_of_polar_geometry monsterCo1Geometry_polar_local_connected
    (monsterCo1PolarLocal_commute_of_line_closure hcover)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
