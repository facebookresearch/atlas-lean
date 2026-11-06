/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1GeometryPolarLocalReduction

/-! The actual monomial stabilizer is transitive on the genuine base polar neighbors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The fixed physical pentad used as a representative of the base polar-neighbor set. -/
def monsterCo1PolarStandardPentad : Finset (Fin 24) :=
  Finset.univ.filter fun i => i.val < 5

/-- Its literal cardinality is five. -/
theorem monsterCo1PolarStandardPentad_card : monsterCo1PolarStandardPentad.card = 5 := by
  decide +kernel

/-- The actual integral lattice representative of the standard pentad frame class. -/
def monsterCo1PolarPentadLattice : leechIntegral :=
  ⟨monsterCo1PolarPentadVector monsterCo1PolarStandardPentad,
    monsterCo1PolarPentadVector_mem _ monsterCo1PolarStandardPentad_card⟩

/-- Actual norm-eight vectors give genuine points of the original Conway geometry. -/
theorem monsterCo1PolarLocal_normEight_point (u : leechIntegral)
    (hn : leechSquareSum u.val = 64) :
    leechHyperbolicCoordinates (leechReduction u) ∈ generatedCo1GeometryPoints := by
  let v : LeechNormEight := ⟨u, hn⟩
  have hv : v ∈ MulAction.orbit leechIsomSubgroup leechNormEightAxis := by
    rw [leechNormEight_orbit_eq_univ]
    trivial
  obtain ⟨e, he⟩ := hv
  refine ⟨leechReduction u, ⟨e, ?_⟩, rfl⟩
  have h := congrArg (fun w : LeechNormEight => leechReduction w.val) he
  exact h

/-- A genuine actual point represented by the standard odd pentad. -/
def monsterCo1PolarPentadPoint : MonsterCo1GeometryPoint :=
  ⟨leechHyperbolicCoordinates (leechReduction monsterCo1PolarPentadLattice),
    monsterCo1PolarLocal_normEight_point _
      (monsterCo1PolarPentadVector_square _ monsterCo1PolarStandardPentad_card)⟩

/-- The standard pentad point is a genuine polar neighbor of the actual base frame. -/
theorem monsterCo1PolarPentadPoint_neighbor :
    monsterCo1GeometryPolarAdjacent monsterCo1GeometryBasePoint monsterCo1PolarPentadPoint := by
  change co1BinaryPolar monsterCo1GeometryBasePoint.val
    (leechHyperbolicCoordinates (leechReduction monsterCo1PolarPentadLattice)) = 1
  rw [monsterCo1PolarLocal_base_pairing _ 0]
  decide +kernel

private theorem polarLocal_sign_monomial (d : golayCode) :
    golaySignIsometry d ∈ golayMonomialSubgroup :=
  ⟨d, 1, by rw [show golayPermutationIsometry 1 = 1 from golayPermutationHom.map_one, mul_one]⟩

private theorem polarLocal_perm_monomial (p : golayAutomorphismSubgroup) :
    golayPermutationIsometry p ∈ golayMonomialSubgroup :=
  ⟨0, p, by rw [show golaySignIsometry 0 = 1 from golaySignHom.map_one, one_mul]⟩

private theorem polarLocal_pentad_reduction (P : Finset (Fin 24)) (hP : P.card = 5) :
    ∃ p : golayAutomorphismSubgroup,
      leechReduction (leechIntegralAction (golayPermutationIsometry p)
        ⟨monsterCo1PolarPentadVector P, monsterCo1PolarPentadVector_mem P hP⟩) =
          leechReduction monsterCo1PolarPentadLattice := by
  obtain ⟨p, hp⟩ := monsterCo1PolarPentad_to_standard P hP
  refine ⟨p, ?_⟩
  have hu : leechIntegralAction (golayPermutationIsometry p)
      ⟨monsterCo1PolarPentadVector P, monsterCo1PolarPentadVector_mem P hP⟩ =
        monsterCo1PolarPentadLattice := by
    apply Subtype.ext
    rw [leechIntegralAction_golayPermutation, hp]
    rfl
  rw [hu]

/-- Every odd norm-eight quotient class is taken to the standard pentad by an actual monomial. -/
theorem monsterCo1PolarLocal_odd_monomial (u : leechIntegral)
    (hn : leechSquareSum u.val = 64) (hodd : (u.val 0 : ZMod 2) = 1) :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧
      leechReduction (leechIntegralAction e u) = leechReduction monsterCo1PolarPentadLattice := by
  obtain ⟨d, hd⟩ := monsterCo1PolarLocal_source_sign u hodd
  let t := leechIntegralAction (golaySignIsometry d) u
  have ht : leechSquareSum t.val = 64 := by rw [leechIntegralAction_squareSum]; exact hn
  rcases monsterCo1PolarLocal_residue_shapes t ht hd with hs | hs
  · obtain ⟨p, hp⟩ := monsterCo1PolarLocal_triple_reduction t ht hd hs
    let P : Finset (Fin 24) := Finset.univ.filter fun i => 3 ≤ i.val ∧ i.val < 8
    have hP : P.card = 5 := by decide +kernel
    obtain ⟨q, hq⟩ := polarLocal_pentad_reduction P hP
    refine ⟨golayPermutationIsometry q * golayPermutationIsometry p * golaySignIsometry d,
      golayMonomialSubgroup.mul_mem (golayMonomialSubgroup.mul_mem
        (polarLocal_perm_monomial q) (polarLocal_perm_monomial p))
        (polarLocal_sign_monomial d), ?_⟩
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    have he := congrArg (leechModTwoAction (golayPermutationIsometry q)) hp
    change leechReduction (leechIntegralAction (golayPermutationIsometry q)
      (leechIntegralAction (golayPermutationIsometry p) t)) =
        leechReduction (leechIntegralAction (golayPermutationIsometry q)
          ⟨monsterCo1PolarPentadVector P, monsterCo1PolarPentadVector_mem P hP⟩) at he
    exact he.trans hq
  · obtain ⟨P, hP, hu⟩ := monsterCo1PolarLocal_normalized_pentad t ht hd hs
    obtain ⟨p, hp⟩ := polarLocal_pentad_reduction P hP
    refine ⟨golayPermutationIsometry p * golaySignIsometry d,
      golayMonomialSubgroup.mul_mem (polarLocal_perm_monomial p)
        (polarLocal_sign_monomial d),
      ?_⟩
    rw [map_mul, LinearEquiv.mul_apply]
    have he : t = ⟨monsterCo1PolarPentadVector P, monsterCo1PolarPentadVector_mem P hP⟩ :=
      Subtype.ext hu
    change leechReduction (leechIntegralAction (golayPermutationIsometry p) t) = _
    rw [he]
    exact hp

/-- Every base polar neighbor is taken to the pentad point within the full base stabilizer. -/
theorem monsterCo1PolarLocal_neighbor_monomial (p : MonsterCo1GeometryPoint)
    (hp : monsterCo1GeometryPolarAdjacent monsterCo1GeometryBasePoint p) :
    ∃ g : Co1, g ∈ monsterCo1GeometryMonomialClasses ∧ g • p = monsterCo1PolarPentadPoint := by
  obtain ⟨u, hn, hu, ho⟩ := monsterCo1PolarLocal_neighbor_representative p hp
  obtain ⟨e, he, hclass⟩ := monsterCo1PolarLocal_odd_monomial u hn (ho 0)
  refine ⟨QuotientGroup.mk e, ⟨⟨e, he⟩, rfl⟩, ?_⟩
  apply Subtype.ext
  change co1BinaryAction (QuotientGroup.mk e) p.val = _
  rw [← hu, monsterCo1GeometryClass_coordinates]
  exact congrArg leechHyperbolicCoordinates hclass

/-- The genuine full base-point stabilizer is transitive on its actual polar-neighbor set. -/
theorem monsterCo1PolarLocal_monomial_transitive (p q : MonsterCo1GeometryPoint)
    (hp : monsterCo1GeometryPolarAdjacent monsterCo1GeometryBasePoint p)
    (hq : monsterCo1GeometryPolarAdjacent monsterCo1GeometryBasePoint q) :
    ∃ g : Co1, g ∈ monsterCo1GeometryMonomialClasses ∧ g • p = q := by
  obtain ⟨a, ha, hap⟩ := monsterCo1PolarLocal_neighbor_monomial p hp
  obtain ⟨b, hb, hbq⟩ := monsterCo1PolarLocal_neighbor_monomial q hq
  refine ⟨b⁻¹ * a, monsterCo1GeometryMonomialClasses.mul_mem
    (monsterCo1GeometryMonomialClasses.inv_mem hb) ha, ?_⟩
  rw [mul_smul, hap, ← hbq, inv_smul_smul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
