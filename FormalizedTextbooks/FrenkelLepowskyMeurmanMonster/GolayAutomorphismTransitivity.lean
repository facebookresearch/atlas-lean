/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismStabilizer

/-! Five-transitivity of the actual Golay automorphism group from the checked
stabilizer representatives. No Mathieu order or transitivity fact is assumed. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The first five entries of the concrete seven-point base are coordinates 0 to 4. -/
theorem golayBasePoints_firstFive : ∀ j : Fin 5,
    golayBasePoints (Fin.castAdd 2 j) = Fin.castAdd 19 j := by
  decide +kernel

private theorem golayAutomorphism_maps_base_prefix (b : Fin 5 → Fin 24)
    (hb : Function.Injective b) : ∀ k : ℕ, k ≤ 5 →
    ∃ p : golayAutomorphismSubgroup, ∀ j : Fin 5, j.val < k → p.val (Fin.castAdd 19 j) = b j := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨1, ?_⟩
    intro j hj
    omega
  | succ k ih =>
    intro hk
    have hk5 : k < 5 := by omega
    obtain ⟨p, hp⟩ := ih (by omega)
    let jnext : Fin 5 := ⟨k, hk5⟩
    let knext : Fin 7 := Fin.castAdd 2 jnext
    let i : Fin 24 := p.val.symm (b jnext)
    have hki : k ≤ i.val := by
      by_contra h
      have hik : i.val < k := by omega
      let jprev : Fin 5 := ⟨i.val, by omega⟩
      have hbase : Fin.castAdd 19 jprev = i := Fin.ext rfl
      have hprev := hp jprev hik
      rw [hbase] at hprev
      have hnew : p.val i = b jnext := p.val.apply_symm_apply _
      have hsame := congrArg Fin.val (hb (hprev.symm.trans hnew))
      change i.val = k at hsame
      omega
    have hi : golayStabilizerOrbitEligible knext i := by
      change (if k < 5 then k ≤ i.val else if k = 5 then 8 ≤ i.val
        else i = 5 ∨ i = 6 ∨ i = 7)
      simp only [hk5, ite_true]
      exact hki
    obtain ⟨q, hq⟩ := golayPointStabilizer_reaches knext i hi
    refine ⟨p * q.val, ?_⟩
    intro j hj
    change p.val (q.val.val (Fin.castAdd 19 j)) = b j
    by_cases hjk : j.val < k
    · rw [← golayBasePoints_firstFive j, q.property (Fin.castAdd 2 j) hjk,
        golayBasePoints_firstFive j, hp j hjk]
    · have hjeq : j = jnext := by apply Fin.ext; change j.val = k; omega
      subst j
      rw [← golayBasePoints_firstFive jnext, hq]
      exact p.val.apply_symm_apply _

/-- Every ordered five-tuple of distinct coordinates is an image of the standard tuple. -/
theorem golayAutomorphism_maps_firstFive (b : Fin 5 → Fin 24) (hb : Function.Injective b) :
    ∃ p : golayAutomorphismSubgroup, ∀ j : Fin 5, p.val (Fin.castAdd 19 j) = b j := by
  obtain ⟨p, hp⟩ := golayAutomorphism_maps_base_prefix b hb 5 (by omega)
  exact ⟨p, fun j => hp j j.isLt⟩

/-- The actual Golay automorphism group is transitive on ordered five-tuples. -/
theorem golayAutomorphism_five_transitive (a b : Fin 5 → Fin 24)
    (ha : Function.Injective a) (hb : Function.Injective b) :
    ∃ p : golayAutomorphismSubgroup, ∀ j : Fin 5, p.val (a j) = b j := by
  obtain ⟨p, hp⟩ := golayAutomorphism_maps_firstFive a ha
  obtain ⟨q, hq⟩ := golayAutomorphism_maps_firstFive b hb
  refine ⟨q * p⁻¹, ?_⟩
  intro j
  change q.val (p.val.symm (a j)) = b j
  rw [← hp j, p.val.symm_apply_apply, hq j]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
