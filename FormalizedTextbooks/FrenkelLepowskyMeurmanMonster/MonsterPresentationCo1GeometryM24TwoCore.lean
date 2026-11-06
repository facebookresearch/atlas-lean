/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual Golay permutation group has no nontrivial normal two-subgroup. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayAutomorphismOrder
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic.Group

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The checked level-zero representatives reach every physical coordinate. -/
theorem monsterCo1GeometryM24_reaches (i : Fin 24) :
    ∃ p : golayAutomorphismSubgroup, p.val 0 = i := by
  obtain ⟨p, hp⟩ := golayPointStabilizer_reaches 0 i (by
    change (if (0 : ℕ) < 5 then 0 ≤ i.val else _)
    simp)
  refine ⟨p.val, ?_⟩
  have hbase : golayBasePoints 0 = 0 := by decide +kernel
  simpa only [hbase] using hp

/-- The checked level-one representatives act transitively on the complement of coordinate zero. -/
theorem monsterCo1GeometryM24_stabilizer_reaches (i j : Fin 24) (hi : i ≠ 0) (hj : j ≠ 0) :
    ∃ p : golayAutomorphismSubgroup, p.val 0 = 0 ∧ p.val i = j := by
  have hbase0 : golayBasePoints 0 = 0 := by decide +kernel
  have hbase1 : golayBasePoints 1 = 1 := by decide +kernel
  have heligible (k : Fin 24) (hk : k ≠ 0) : golayStabilizerOrbitEligible 1 k := by
    have hval : k.val ≠ 0 := fun h => hk (Fin.ext h)
    change (if (1 : ℕ) < 5 then 1 ≤ k.val else _)
    simp only [show (1 : ℕ) < 5 by omega, ite_true]
    omega
  obtain ⟨pi, hpi⟩ := golayPointStabilizer_reaches 1 i (heligible i hi)
  obtain ⟨pj, hpj⟩ := golayPointStabilizer_reaches 1 j (heligible j hj)
  have hi0 : pi.val.val 0 = 0 := by
    simpa only [hbase0] using pi.property 0 (by decide)
  have hj0 : pj.val.val 0 = 0 := by
    simpa only [hbase0] using pj.property 0 (by decide)
  have hi1 : pi.val.val 1 = i := by simpa only [hbase1] using hpi
  have hj1 : pj.val.val 1 = j := by simpa only [hbase1] using hpj
  refine ⟨pj.val * pi.val⁻¹, ?_, ?_⟩
  · change pj.val.val (pi.val.val.symm 0) = 0
    have hinv : pi.val.val.symm 0 = 0 := by
      simpa only [Equiv.symm_apply_apply] using (congrArg pi.val.val.symm hi0).symm
    rw [hinv, hj0]
  · change pj.val.val (pi.val.val.symm i) = j
    rw [← hi1, pi.val.val.symm_apply_apply, hj1]

/-- A normal subgroup orbit at coordinate zero is a singleton or the entire physical point set. -/
theorem monsterCo1GeometryM24_normal_orbit (P : Subgroup golayAutomorphismSubgroup)
    [P.Normal] : MulAction.orbit P (0 : Fin 24) = {0} ∨
      MulAction.orbit P (0 : Fin 24) = Set.univ := by
  by_cases hn : ∃ i : Fin 24, i ≠ 0 ∧ i ∈ MulAction.orbit P (0 : Fin 24)
  · right
    apply Set.eq_univ_of_forall
    intro j
    by_cases hj : j = 0
    · subst j
      exact MulAction.mem_orbit_self _
    obtain ⟨i, hi, u, hu⟩ := hn
    change u • (0 : Fin 24) = i at hu
    obtain ⟨p, hp0, hpij⟩ := monsterCo1GeometryM24_stabilizer_reaches i j hi hj
    let v : P := ⟨p * u.val * p⁻¹, (inferInstance : P.Normal).conj_mem u.val u.property p⟩
    refine ⟨v, ?_⟩
    change p.val (u.val.val (p.val.symm 0)) = j
    rw [← hp0, p.val.symm_apply_apply]
    change p.val (u • (0 : Fin 24)) = j
    rw [hu, hpij]
  · left
    apply Set.Subset.antisymm
    · intro i hi
      by_contra h
      exact hn ⟨i, (by simpa only [Set.mem_singleton_iff] using h), hi⟩
    · intro i hi
      rw [Set.mem_singleton_iff] at hi
      subst i
      exact MulAction.mem_orbit_self _

/-- Normal two-subgroups cannot have the orbit of size 24, so they fix coordinate zero. -/
theorem monsterCo1GeometryM24_normal_two_fixes_zero
    (P : Subgroup golayAutomorphismSubgroup) [P.Normal] (hP : IsPGroup 2 P)
    (p : P) : p.val.val 0 = 0 := by
  rcases monsterCo1GeometryM24_normal_orbit P with hsingle | hfull
  · have hp : p • (0 : Fin 24) ∈ MulAction.orbit P (0 : Fin 24) := ⟨p, rfl⟩
    rw [hsingle, Set.mem_singleton_iff] at hp
    exact hp
  · obtain ⟨n, hn⟩ := hP.card_orbit (0 : Fin 24)
    have hcard : Nat.card (MulAction.orbit P (0 : Fin 24)) = 24 := by
      rw [hfull, Nat.card_eq_fintype_card]
      simp
    rw [hcard] at hn
    have h3 : 3 ∣ (2 : ℕ) ^ n := by rw [← hn]; decide
    have h32 := Nat.prime_three.dvd_of_dvd_pow h3
    norm_num at h32

/-- The actual degree-24 Golay permutation group has no nontrivial normal two-subgroup. -/
theorem monsterCo1GeometryM24_normal_two_eq_bot
    (P : Subgroup golayAutomorphismSubgroup) [P.Normal] (hP : IsPGroup 2 P) : P = ⊥ := by
  apply le_antisymm _ bot_le
  intro p hp
  change p = 1
  apply Subtype.ext
  apply Equiv.ext
  intro i
  obtain ⟨r, hr⟩ := monsterCo1GeometryM24_reaches i
  let v : P := ⟨r⁻¹ * p * r, (inferInstance : P.Normal).conj_mem p hp r⁻¹⟩
  have hv := monsterCo1GeometryM24_normal_two_fixes_zero P hP v
  change r.val.symm (p.val (r.val 0)) = 0 at hv
  rw [hr] at hv
  have he := congrArg r.val hv
  change p.val i = i
  simpa only [Equiv.apply_symm_apply, hr] using he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
