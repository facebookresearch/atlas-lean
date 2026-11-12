/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner
-/
module

public import MathlibExt.SetTheory.InfinitaryCombinatorics.AlmostDisjoint

@[expose] public section

open Cardinal Ordinal

namespace MathlibExtTest.SetTheory.InfinitaryCombinatorics.AlmostDisjoint

open MetaMathlibExt

-- Logic 25: Almost disjoint family

/-- Sanity check: evens and odds form an almost disjoint family at `ℵ₀`. -/

theorem evens_odds_isAlmostDisjointFamilyKappa :
    IsAlmostDisjointFamilyKappa ℵ₀
      ({Set.range (fun n : ℕ => 2 * n), Set.range (fun n : ℕ => 2 * n + 1)} :
        Set (Set ℕ)) := by
  have hinj1 : Function.Injective (fun n : ℕ => 2 * n) := by intro a b h; simpa using h
  have hinj2 : Function.Injective (fun n : ℕ => 2 * n + 1) := by intro a b h; simpa using h
  have hc1 : #(Set.range (fun n : ℕ => 2 * n)) = ℵ₀ := by
    rw [Cardinal.mk_range_eq _ hinj1]; simp
  have hc2 : #(Set.range (fun n : ℕ => 2 * n + 1)) = ℵ₀ := by
    rw [Cardinal.mk_range_eq _ hinj2]; simp
  have hdisj :
      Set.range (fun n : ℕ => 2 * n) ∩ Set.range (fun n : ℕ => 2 * n + 1) = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_empty_iff_false, iff_false, not_and]
    rintro ⟨n, rfl⟩ ⟨m, hm⟩
    omega
  constructor
  · rintro B hB
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hB
    rcases hB with rfl | rfl
    · exact hc1
    · exact hc2
  · rintro B hB C hC hBC
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hB hC
    rcases hB with rfl | rfl <;> rcases hC with rfl | rfl
    · exact absurd rfl hBC
    · rw [hdisj]; simp [aleph0_pos]
    · rw [Set.inter_comm, hdisj]; simp [aleph0_pos]
    · exact absurd rfl hBC

-- Logic 21: Almost disjoint modulo the nonstationary ideal

/-- Agreement on a nonempty nonstationary set still counts as almost disjoint: these functions
    agree only at `0`, and `{0}` is not stationary (the club `(0, ω₁)` misses it). -/

theorem almostDisjointModNS_agree_at_zero :
    AlmostDisjointModNS.{0} (A := fun _ => Bool)
      (fun α => decide (α.1 = 0)) (fun _ => true) := by
  have h1 : (1 : Ordinal.{0}) < (Cardinal.aleph 1 : Cardinal.{0}).ord := by
    rw [Cardinal.lt_ord, Ordinal.card_one]
    exact Cardinal.one_lt_aleph0.trans Cardinal.aleph0_lt_aleph_one
  have h0 : (0 : Ordinal.{0}) < (Cardinal.aleph 1 : Cardinal.{0}).ord := zero_lt_one.trans h1
  rw [AlmostDisjointModNS, not_isStationary_iff]
  refine ⟨Set.Ioi ⟨0, h0⟩,
    ⟨(isUpperSet_Ioi (a := (⟨0, h0⟩ : Set.Iio (Cardinal.aleph 1 : Cardinal.{0}).ord))).dirSupClosed,
      fun x => ?_⟩, ?_⟩
  · by_cases hx : x.1 = 0
    · refine ⟨⟨1, h1⟩, ?_, ?_⟩
      · show (0 : Ordinal) < 1
        exact zero_lt_one
      · show x.1 ≤ 1
        rw [hx]
        exact zero_le_one
    · exact ⟨x, show (0 : Ordinal) < x.1 from pos_iff_ne_zero.mpr hx, le_rfl⟩
  · rw [Set.disjoint_left]
    intro α hα hlt
    simp only [Set.mem_setOf_eq, decide_eq_true_eq] at hα
    have h : (0 : Ordinal) < α.1 := hlt
    rw [hα] at h
    exact lt_irrefl _ h

-- Logic 54: Almost disjoint family of functions

theorem isAlmostDisjointFunFamily_pair_const.{u} {κ : Cardinal.{u}} (hκ : 0 < κ)
    {a b : Set.Iio κ.ord} (hab : a ≠ b) :
    IsAlmostDisjointFunFamily {(fun _ => a), (fun _ => b)} := by
  have key : ∀ x y : Set.Iio κ.ord, x ≠ y →
      #{α : Set.Iio κ.ord | (fun _ => x) α = (fun _ => y) α} < Cardinal.lift.{u+1} κ := by
    intro x y hxy
    have hemp : {α : Set.Iio κ.ord | (fun _ => x) α = (fun _ => y) α} = ∅ := by
      ext α; simp [hxy]
    rw [hemp]
    simpa using hκ
  rintro f hf g hg hfg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf hg
  rcases hf with rfl | rfl <;> rcases hg with rfl | rfl
  · exact absurd rfl hfg
  · exact key a b hab
  · exact key b a hab.symm
  · exact absurd rfl hfg

end MathlibExtTest.SetTheory.InfinitaryCombinatorics.AlmostDisjoint

end
