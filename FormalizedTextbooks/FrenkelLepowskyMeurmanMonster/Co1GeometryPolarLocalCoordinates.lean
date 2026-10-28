/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1GeometryPolarLocalTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightPreparationMonomial

/-! The actual base polar functional is physical coordinate parity. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The actual polar functional at the distinguished frame reads hyperbolic coordinate 23. -/
theorem monsterCo1PolarBase_apply (v : Fin 24 → ZMod 2) :
    co1BinaryPolar monsterCo1GeometryBasePoint.val v = v 23 := by
  rw [monsterCo1GeometryBasePoint_binary]
  change qBeta (Pi.single 11 1) v + qBeta v (Pi.single 11 1) = v 23
  change qBeta (Pi.single (Fin.castAdd 12 (11 : Fin 12)) 1) v +
    qBeta v (Pi.single (Fin.castAdd 12 (11 : Fin 12)) 1) = _
  rw [qBeta_single_first, qBeta_right_single_first, add_zero]
  rfl

/-- Physical parity is exactly the last hyperbolic coordinate on the genuine lattice quotient. -/
theorem monsterCo1PolarLocal_physical_parity (u : leechIntegral) (i : Fin 24) :
    (u.val i : ZMod 2) = (leechHyperbolicCoordinates (leechReduction u)) 23 := by
  rw [← leechExplicitCoordinates_vector u, leechHyperbolicCoordinates_explicit]
  have hrow : ∀ i j : Fin 24,
      (leechBasisMatrix i j : ZMod 2) = leechHyperbolicInverse 23 j := by
    decide +kernel
  simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [hrow]
  rfl

/-- The polar pairing with the actual base frame is the parity of any physical coordinate. -/
theorem monsterCo1PolarLocal_base_pairing (u : leechIntegral) (i : Fin 24) :
    co1BinaryPolar monsterCo1GeometryBasePoint.val
      (leechHyperbolicCoordinates (leechReduction u)) = (u.val i : ZMod 2) := by
  rw [monsterCo1PolarBase_apply]
  exact (monsterCo1PolarLocal_physical_parity u i).symm

/-- Every genuine geometry point has an actual norm-eight lattice representative. -/
theorem monsterCo1PolarLocal_point_representative (p : MonsterCo1GeometryPoint) :
    ∃ u : leechIntegral, leechSquareSum u.val = 64 ∧
      leechHyperbolicCoordinates (leechReduction u) = p.val := by
  obtain ⟨g, hg⟩ := monsterCo1GeometryPoint_reached p
  obtain ⟨e, he⟩ := QuotientGroup.mk'_surjective signsSubgroup g
  refine ⟨leechIntegralAction e (leechCoordinateFrameLattice 0), ?_, ?_⟩
  · rw [leechIntegralAction_squareSum]
    exact leechCoordinateFrameVector_square 0
  · change leechHyperbolicCoordinates (leechModTwoAction e
      (leechReduction (leechCoordinateFrameLattice 0))) = p.val
    rw [← monsterCo1GeometryClass_coordinates]
    rw [← monsterCo1GeometryBasePoint_value]
    change ((QuotientGroup.mk e : Co1) • monsterCo1GeometryBasePoint).val = p.val
    have he' : (QuotientGroup.mk e : Co1) = g := he
    rw [he', hg]

/-- A polar neighbor of the actual base has odd residue in every physical coordinate. -/
theorem monsterCo1PolarLocal_neighbor_representative
    (p : MonsterCo1GeometryPoint) (hp : monsterCo1GeometryPolarAdjacent
      monsterCo1GeometryBasePoint p) :
    ∃ u : leechIntegral, leechSquareSum u.val = 64 ∧
      leechHyperbolicCoordinates (leechReduction u) = p.val ∧
      ∀ i : Fin 24, (u.val i : ZMod 2) = 1 := by
  obtain ⟨u, hn, hu⟩ := monsterCo1PolarLocal_point_representative p
  refine ⟨u, hn, hu, ?_⟩
  intro i
  rw [← monsterCo1PolarLocal_base_pairing u i, hu]
  exact hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
