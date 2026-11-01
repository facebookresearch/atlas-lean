/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOrderCounting
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedOrbitStabilizers
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.AxisTransitionCounts
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.FeasibleAxisTransitionCounts

/-! Connecting the source transition tables to counts of the actual G-orbits.

The balance, anchor, and common-stabilizer inputs below are explicit remaining
certificate and local-group obligations. They are not asserted to be proved.
In particular a freely supplied vector of the expected numbers cannot satisfy
these interfaces: the vector consists of cardinalities of fibers of a
classification of the actual orbit. See Höhn--Seysen, arXiv:2508.01037, §§3--5. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Matrix

/-- The count vector of an actual classification, in rational arithmetic. -/
noncomputable def classifiedOrbitCountVector {α : Type*} {n : ℕ}
    (κ : α → Fin n) : Fin n → ℚ :=
  fun i => (Nat.card {x : α // κ x = i} : ℚ)

/-- A classification partitions the entire finite type, regardless of whether
its labels correctly identify local-group orbits. -/
theorem classifiedOrbitCountVector_sum {α : Type*} [Finite α] {n : ℕ}
    (κ : α → Fin n) :
    (∑ i, classifiedOrbitCountVector κ i) = (Nat.card α : ℚ) := by
  have h : (∑ i, Nat.card {x : α // κ x = i}) = Nat.card α := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr (Equiv.sigmaFiberEquiv κ)
  unfold classifiedOrbitCountVector
  exact_mod_cast h

/-- The source axis table determines the size of an actual orbit once its
actual classification-fiber counts satisfy the certificate balance and anchor. -/
theorem generatedVectorOrbit_card_of_transition (a : GriessSpace)
    (κ : generatedVectorOrbit a → Fin 12)
    (hbalance : monsterAxisTransitionMatrix *ᵥ classifiedOrbitCountVector κ =
      (16584750 : ℚ) • classifiedOrbitCountVector κ)
    (hanchor : classifiedOrbitCountVector κ 0 = 196560) :
    Nat.card (generatedVectorOrbit a) = 97239461142009186000 := by
  have : Finite G := generated_group_finite_of_triality_product sExtra_preserves_griessProd
  have : Finite (generatedVectorOrbit a) := by
    rw [generatedVectorOrbit_eq_action_orbit]
    exact (Finite.finite_mulAction_orbit (M := G) a).to_subtype
  have h := monster_axis_count_sum_of_transition (classifiedOrbitCountVector κ) hbalance hanchor
  rw [classifiedOrbitCountVector_sum] at h
  exact_mod_cast h

/-- The feasible-axis table determines the size of the actual second orbit
under the actual first stabilizer, with its certificate obligations explicit. -/
theorem generatedFeasibleVectorOrbit_card_of_transition (a b : GriessSpace)
    (κ : generatedFeasibleVectorOrbit a b → Fin 10)
    (hbalance : feasibleAxisTransitionMatrix *ᵥ classifiedOrbitCountVector κ =
      (93150 : ℚ) • classifiedOrbitCountVector κ)
    (hanchor : classifiedOrbitCountVector κ 0 = 1) :
    Nat.card (generatedFeasibleVectorOrbit a b) = 11707448673375 := by
  have : Finite G := generated_group_finite_of_triality_product sExtra_preserves_griessProd
  have : Finite (generatedFeasibleVectorOrbit a b) :=
    (Finite.finite_mulAction_orbit (M := generatedVectorStabilizer a) b).to_subtype
  have h := feasible_axis_count_sum_of_transition (classifiedOrbitCountVector κ) hbalance hanchor
  rw [classifiedOrbitCountVector_sum] at h
  exact_mod_cast h

/-- The exact remaining inputs of the constructive two-axis order route.
The order conclusion is conditional on actual-orbit transition balances,
their anchors, and the actual common-stabilizer count. -/
theorem generated_group_order_of_axis_transition_counts (a b : GriessSpace)
    (κ : generatedVectorOrbit a → Fin 12)
    (κ' : generatedFeasibleVectorOrbit a b → Fin 10)
    (hbalance : monsterAxisTransitionMatrix *ᵥ classifiedOrbitCountVector κ =
      (16584750 : ℚ) • classifiedOrbitCountVector κ)
    (hanchor : classifiedOrbitCountVector κ 0 = 196560)
    (hbalance' : feasibleAxisTransitionMatrix *ᵥ classifiedOrbitCountVector κ' =
      (93150 : ℚ) • classifiedOrbitCountVector κ')
    (hanchor' : classifiedOrbitCountVector κ' 0 = 1)
    (hpair : Nat.card (generatedVectorPairStabilizer a b) = 2 ^ 24 * 42305421312000) :
    Nat.card G =
      2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 *
      17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71 := by
  rw [generated_card_eq_two_vector_orbits_mul_pair_stabilizer,
    generatedVectorOrbit_card_of_transition a κ hbalance hanchor,
    generatedFeasibleVectorOrbit_card_of_transition a b κ' hbalance' hanchor', hpair]
  norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
