/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleSecondaryOutsideOctadOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormEightPreparationMonomial

/-! Actual disjoint coordinate-pair lines and original monomial normalization. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Original perpendicular pair labels after removing the actual plus-pair mate. -/
def generatedFeasibleDisjointPairLabels : Finset (Fin 2 × Fin 276) :=
  generatedFeasibleOrthogonalPairLabels.erase (1, generatedFeasiblePhysicalRootPair)

/-- The actual plus-pair mate belongs to the original perpendicular pair catalogue. -/
theorem generatedFeasibleDisjointPair_mate_mem :
    (1, generatedFeasiblePhysicalRootPair) ∈ generatedFeasibleOrthogonalPairLabels := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  simp [griessShortIntegral, generatedFeasiblePhysicalRootPair_coordinates]

/-- Exactly462 original preferred coordinate-pair lines have support disjoint from the root pair. -/
theorem generatedFeasibleDisjointPairLabels_card :
    generatedFeasibleDisjointPairLabels.card = 462 := by
  rw [generatedFeasibleDisjointPairLabels, Finset.card_erase_of_mem
    generatedFeasibleDisjointPair_mate_mem, generatedFeasibleOrthogonalPairLabels_card]

set_option maxHeartbeats 8000000 in
-- Check all original increasing physical pairs and both actual preferred sign families.
private theorem disjointPair_physical_check : ∀ s : Fin 2, ∀ a b : Fin 24, a < b →
    ((¬(s = 1 ∧ a = 0 ∧ b = 1) ∧
      4 * (if (0 : Fin 24) = a then (1 : ℤ) else 0) +
        (if s = 0 then -4 else 4) * (if (0 : Fin 24) = b then 1 else 0) =
      4 * (if (1 : Fin 24) = a then (1 : ℤ) else 0) +
        (if s = 0 then -4 else 4) * (if (1 : Fin 24) = b then 1 else 0)) ↔
      2 ≤ a.val ∧ 2 ≤ b.val) := by
  decide +kernel

/-- The retained original pair catalogue is exactly the sector outside coordinates0 and1. -/
theorem generatedFeasibleDisjointPair_support (s : Fin 2) (p : Fin 276) :
    (s, p) ∈ generatedFeasibleDisjointPairLabels ↔
      2 ≤ (griessCoordinatePair p).1.val ∧ 2 ≤ (griessCoordinatePair p).2.val := by
  have hindex : p = generatedFeasiblePhysicalRootPair ↔ griessCoordinatePair p = (0, 1) := by
    constructor
    · rintro rfl
      exact generatedFeasiblePhysicalRootPair_coordinates
    · intro h
      apply griessCoordinatePairEquiv.injective
      apply Subtype.ext
      exact h.trans generatedFeasiblePhysicalRootPair_coordinates.symm
  have hp : (s, p) = (1, generatedFeasiblePhysicalRootPair) ↔
      s = 1 ∧ (griessCoordinatePair p).1 = 0 ∧ (griessCoordinatePair p).2 = 1 := by
    rw [Prod.mk.injEq, hindex]
    exact and_congr_right fun _ => Prod.ext_iff
  have hlt := (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2
  change (griessCoordinatePair p).1 < (griessCoordinatePair p).2 at hlt
  simp only [generatedFeasibleDisjointPairLabels, Finset.mem_erase, ne_eq, hp,
    generatedFeasibleOrthogonalPairLabels, Finset.mem_filter, Finset.mem_univ,
    true_and, griessShortIntegral]
  exact disjointPair_physical_check s _ _ hlt

/-- Every original perpendicular pair line is the actual mate or a genuine disjoint pair. -/
theorem generatedFeasibleDisjointPair_partition (z : Fin 2 × Fin 276) :
    z ∈ generatedFeasibleOrthogonalPairLabels ↔
      z = (1, generatedFeasiblePhysicalRootPair) ∨ z ∈ generatedFeasibleDisjointPairLabels := by
  constructor
  · intro hz
    by_cases he : z = (1, generatedFeasiblePhysicalRootPair)
    · exact Or.inl he
    · exact Or.inr (Finset.mem_erase.mpr ⟨he, hz⟩)
  · rintro (rfl | hz)
    · exact generatedFeasibleDisjointPair_mate_mem
    · exact Finset.mem_of_mem_erase hz

/-- The actual coordinate-pair dictionary address of physical coordinates2 and3. -/
def generatedFeasibleDisjointPairPrototypeIndex : Fin 276 :=
  griessPairIndex 2 3 (by decide)

/-- The prototype index is bound to the two original physical coordinates. -/
theorem generatedFeasibleDisjointPairPrototype_coordinates :
    griessCoordinatePair generatedFeasibleDisjointPairPrototypeIndex = (2, 3) := by
  rw [generatedFeasibleDisjointPairPrototypeIndex, griessPairIndex_coordinates]
  rfl

/-- The original preferred minus-pair prototype at coordinates2 and3. -/
def generatedFeasibleDisjointPairPrototypeLabel : GriessShortIndex :=
  Sum.inl (0, generatedFeasibleDisjointPairPrototypeIndex)

/-- The actual preferred prototype is the original integral vector4(e2-e3). -/
theorem generatedFeasibleDisjointPairPrototype_integral (i : Fin 24) :
    griessShortIntegral generatedFeasibleDisjointPairPrototypeLabel i =
      4 * (if i = 2 then 1 else 0) - 4 * (if i = 3 then 1 else 0) := by
  simp only [generatedFeasibleDisjointPairPrototypeLabel, griessShortIntegral,
    generatedFeasibleDisjointPairPrototype_coordinates, ite_true]
  ring

/-- The actual prototype belongs to the original disjoint-pair catalogue. -/
theorem generatedFeasibleDisjointPairPrototype_mem :
    (0, generatedFeasibleDisjointPairPrototypeIndex) ∈ generatedFeasibleDisjointPairLabels := by
  rw [generatedFeasibleDisjointPair_support, generatedFeasibleDisjointPairPrototype_coordinates]
  decide

/-- The original short labels of disjoint pairs avoid both preferred root-pair lines. -/
theorem generatedFeasibleDisjointPair_ne_root (s : Fin 2) (p : Fin 276)
    (hp : (s, p) ∈ generatedFeasibleDisjointPairLabels) (a : Fin 2) :
    Sum.inl (s, p) ≠ (Sum.inl (a, generatedFeasiblePhysicalRootPair) : GriessShortIndex) := by
  intro he
  have hh := Sum.inl_injective he
  have hcoord := (generatedFeasibleDisjointPair_support s p).mp hp
  have hindex : p = generatedFeasiblePhysicalRootPair := congrArg Prod.snd hh
  rw [hindex, generatedFeasiblePhysicalRootPair_coordinates] at hcoord
  norm_num at hcoord

/-- Every actual disjoint-pair preferred line is outside the original first/Omega binary plane. -/
theorem generatedFeasibleDisjointPair_independent (s : Fin 2) (p : Fin 276)
    (hp : (s, p) ∈ generatedFeasibleDisjointPairLabels) :
    (griessShortQ (Sum.inl (s, p))).base ≠
        (griessShortQ (Sum.inl (0, generatedFeasiblePhysicalRootPair))).base ∧
      toAdd (griessShortQ (Sum.inl (s, p))).base ≠ toAdd sourceOmegaQ.base +
        toAdd (griessShortQ (Sum.inl (0, generatedFeasiblePhysicalRootPair))).base := by
  constructor
  · intro h
    exact generatedFeasibleDisjointPair_ne_root s p hp 0
      (generatedFeasible_short_base_injective h)
  · intro h
    rw [← generatedFeasible_pair_mate_base] at h
    exact generatedFeasibleDisjointPair_ne_root s p hp 1
      (generatedFeasible_short_base_injective (toAdd.injective h))

set_option maxHeartbeats 8000000 in
-- Bind the original four-point word and all pair coordinates before preferred-class transport.
/-- Every actual disjoint preferred pair has an original monomial transport to the prototype
fixing the first preferred root line. -/
theorem generatedFeasibleDisjointPair_monomial (s : Fin 2) (p : Fin 276)
    (hp : (s, p) ∈ generatedFeasibleDisjointPairLabels) :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧
      griessShortPermutation e (Sum.inl (0, generatedFeasiblePhysicalRootPair)) =
        Sum.inl (0, generatedFeasiblePhysicalRootPair) ∧
      griessShortPermutation e (Sum.inl (s, p)) = generatedFeasibleDisjointPairPrototypeLabel := by
  let a := (griessCoordinatePair p).1
  let b := (griessCoordinatePair p).2
  have hab : a ≠ b := griessCoordinatePair_ne p
  have houtside := (generatedFeasibleDisjointPair_support s p).mp hp
  have ht : Function.Injective (![0, 1, a, b] : Fin 4 → Fin 24) := by
    intro i j he
    have hh := congrArg (fun k : Fin 24 => k.val) he
    fin_cases i <;> fin_cases j <;> simp_all [a, b] <;> omega
  obtain ⟨q, hq⟩ := golayAutomorphism_four_transitive ![0, 1, a, b] ![0, 1, 2, 3]
    ht (by intro i j he; fin_cases i <;> fin_cases j <;> simp_all)
  have hq0 : q.val 0 = 0 := hq 0
  have hq1 : q.val 1 = 1 := hq 1
  have hqa : q.val a = 2 := hq 2
  have hqb : q.val b = 3 := hq 3
  let u := griessShortLatticeVector (Sum.inl (s, p))
  let v := leechIntegralAction (golayPermutationIsometry q) u
  have hv (i : Fin 24) : v.val i =
      4 * (if i = 2 then 1 else 0) + (if s = 0 then -4 else 4) * (if i = 3 then 1 else 0) := by
    change (leechIntegralAction (golayPermutationIsometry q) u).val i = _
    rw [leechIntegralAction_golayPermutation]
    have ha : q.val.symm i = a ↔ i = 2 := by rw [Equiv.symm_apply_eq, hqa]
    have hb : q.val.symm i = b ↔ i = 3 := by rw [Equiv.symm_apply_eq, hqb]
    simp only [golayIntegerPermute, u, griessShortLatticeVector, griessShortIntegral,
      a, b, ha, hb]
  let bits : Fin 4 → ZMod 2 := ![0, 0, 0, if s = 0 then 0 else 1]
  obtain ⟨d, hd⟩ := golayCode_four_coordinate_surjective
    (fun j : Fin 4 => Fin.castAdd 20 j)
    (by intro i j he; exact Fin.ext (congrArg (fun k : Fin 24 => k.val) he)) bits
  have hd0 : d.val 0 = 0 := congrFun hd 0
  have hd1 : d.val 1 = 0 := congrFun hd 1
  have hd2 : d.val 2 = 0 := congrFun hd 2
  have hd3 : d.val 3 = if s = 0 then 0 else 1 := congrFun hd 3
  have hpos : (leechIntegralAction (golaySignIsometry d) v).val =
      griessShortIntegral generatedFeasibleDisjointPairPrototypeLabel := by
    rw [leechIntegralAction_golaySign]
    funext i
    rw [generatedFeasibleDisjointPairPrototype_integral]
    change (if d.val i = 0 then v.val i else -v.val i) = _
    rw [hv]
    by_cases h2 : i = 2
    · subst i
      simp [hd2]
    · by_cases h3 : i = 3
      · subst i
        rw [hd3]
        fin_cases s <;> norm_num
      · simp [h2, h3]
  let e := golaySignIsometry d * golayPermutationIsometry q
  have he : e ∈ golayMonomialSubgroup := ⟨d, q, rfl⟩
  have hplus : griessShortPermutation e leechRootedA2RootAddress = leechRootedA2RootAddress := by
    apply (leechRootedA2RootLineSubgroup_mem e).mpr
    exact leechRootedA2PreservesRootLine_mul _ _ (leechRootedA2Root_sign d (hd0.trans hd1.symm))
      (Or.inl (leechRootedA2Root_permutation q hq0 hq1))
  change griessShortPermutation e (Sum.inl (1, generatedFeasiblePhysicalRootPair)) =
    Sum.inl (1, generatedFeasiblePhysicalRootPair) at hplus
  refine ⟨e, he, (generatedFeasible_monomial_pair_fix_iff e he).mpr hplus, ?_⟩
  apply (leechRootedA2_short_perm_eq_iff _ _ _).mpr
  left
  apply Subtype.ext
  rw [map_mul, LinearEquiv.mul_apply]
  exact hpos

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
