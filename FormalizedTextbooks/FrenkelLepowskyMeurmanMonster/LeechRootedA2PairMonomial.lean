/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2RootLine
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechShortTransitivityCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationMonomialFamilies

/-! Actual root-line-preserving monomial normalization of neighboring pair short vectors. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Three-transitivity follows by extending tuples and applying actual Mathieu four-transitivity. -/
theorem leechRootedA2_three_transitive (a b : Fin 3 → Fin 24)
    (ha : Function.Injective a) (hb : Function.Injective b) :
    ∃ p : golayAutomorphismSubgroup, ∀ j, p.val (a j) = b j := by
  obtain ⟨a', ha', hea⟩ := leechShort_extend_tuple (by decide : 3 < 24) a ha
  obtain ⟨b', hb', heb⟩ := leechShort_extend_tuple (by decide : 3 < 24) b hb
  obtain ⟨p, hp⟩ := golayAutomorphism_four_transitive a' b' ha' hb'
  exact ⟨p, fun j => by simpa only [hea, heb] using hp j.castSucc⟩

/-- Move a selected root coordinate and an outside coordinate to0 and2, preserving the root pair. -/
theorem leechRootedA2Pair_permutation (i j : Fin 24) (hi : i.val < 2) (hj : 2 ≤ j.val) :
    ∃ p : golayAutomorphismSubgroup, p.val i = 0 ∧ p.val j = 2 ∧
      leechIntegralAction (golayPermutationIsometry p) leechRootedA2Root =
        leechRootedA2Root := by
  let a : Fin 3 → Fin 24 := ![0, 1, j]
  have ha : Function.Injective a := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [a]
    all_goals omega
  by_cases hi0 : i = 0
  · let b : Fin 3 → Fin 24 := ![0, 1, 2]
    have hb : Function.Injective b := by decide +kernel
    obtain ⟨p, hp⟩ := leechRootedA2_three_transitive a b ha hb
    have hp0 : p.val 0 = 0 := hp 0
    have hp1 : p.val 1 = 1 := hp 1
    exact ⟨p, by simpa only [hi0] using hp0, hp 2,
      leechRootedA2Root_permutation p hp0 hp1⟩
  · have hi1 : i = 1 := by apply Fin.ext; have hv := Fin.val_ne_iff.mpr hi0; omega
    let b : Fin 3 → Fin 24 := ![1, 0, 2]
    have hb : Function.Injective b := by decide +kernel
    obtain ⟨p, hp⟩ := leechRootedA2_three_transitive a b ha hb
    have hp0 : p.val 0 = 1 := hp 0
    have hp1 : p.val 1 = 0 := hp 1
    exact ⟨p, by simpa only [hi1] using hp1, hp 2,
      leechRootedA2Root_permutation_swap p hp0 hp1⟩

/-- The positive standard pair neighbor of the fixed root. -/
def leechRootedA2PositivePair : Fin 24 → ℤ := fun i =>
  4 * (if i = 0 then 1 else 0) + 4 * (if i = 2 then 1 else 0)

/-- Every original neighboring pair short vector reaches the same target preserving root line. -/
theorem leechRootedA2Pair_monomial_reduction (s : Fin 2) (q : Fin 276)
    (hr : leechRootedA2NeighborPredicate (Sum.inl (s, q))) :
    ∃ e : leechIsomSubgroup, e ∈ golayMonomialSubgroup ∧
      leechRootedA2PreservesRootLine e ∧
      (leechIntegralAction e (griessShortLatticeVector (Sum.inl (s, q)))).val =
        leechRootedA2PositivePair := by
  have hh := (leechRootedA2Pair_neighbor_iff s q).mp hr
  obtain ⟨p, hpi, hpj, hpr⟩ := leechRootedA2Pair_permutation
    (griessCoordinatePair q).1 (griessCoordinatePair q).2 hh.1 hh.2
  let u := griessShortLatticeVector (Sum.inl (s, q))
  let v := leechIntegralAction (golayPermutationIsometry p) u
  have hv : v.val = fun i =>
      4 * (if i = 0 then (1 : ℤ) else 0) +
        (if s = 0 then -4 else 4) * (if i = 2 then 1 else 0) := by
    rw [leechIntegralAction_golayPermutation]
    funext i
    have hpa : p.val.symm i = (griessCoordinatePair q).1 ↔ i = 0 := by
      rw [p.val.symm_apply_eq, hpi]
    have hpb : p.val.symm i = (griessCoordinatePair q).2 ↔ i = 2 := by
      rw [p.val.symm_apply_eq, hpj]
    simp only [golayIntegerPermute, u, griessShortLatticeVector, griessShortIntegral, hpa, hpb]
  let f : Fin 3 → Fin 24 := fun j => Fin.castAdd 21 j
  have hf : Function.Injective f := by
    intro j k h
    exact Fin.ext (congrArg (fun i : Fin 24 => i.val) h)
  obtain ⟨d, hd⟩ := golayCoordinateProjection_surjective (by decide : 3 < 8) f hf
    ![0, 0, if s = 0 then (1 : ZMod 2) else 0]
  have hd0 : d.val 0 = 0 := congrFun hd 0
  have hd1 : d.val 1 = 0 := congrFun hd 1
  have hd2 : d.val 2 = if s = 0 then 1 else 0 := congrFun hd 2
  refine ⟨golaySignIsometry d * golayPermutationIsometry p, ⟨d, p, rfl⟩,
    leechRootedA2PreservesRootLine_mul _ _
      (leechRootedA2Root_sign d (hd0.trans hd1.symm)) (Or.inl hpr), ?_⟩
  rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign]
  change golayIntegerSign d.val v.val = leechRootedA2PositivePair
  rw [hv]
  funext i
  by_cases hi0 : i = 0
  · subst i
    simp [golayIntegerSign, leechRootedA2PositivePair, hd0]
  · by_cases hi2 : i = 2
    · subst i
      by_cases hs : s = 0 <;> simp [golayIntegerSign, leechRootedA2PositivePair, hd2, hs]
    · simp [golayIntegerSign, leechRootedA2PositivePair, hi0, hi2]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
