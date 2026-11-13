/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace StatMech.Onsager

def onsTorusAdj (L : ℕ) (u v : ZMod L × ZMod L) : Prop :=
  (u.1 = v.1 ∧ (u.2 = v.2 + 1 ∨ u.2 = v.2 - 1)) ∨ (u.2 = v.2 ∧ (u.1 = v.1 + 1 ∨ u.1 = v.1 - 1))

instance (L : ℕ) : DecidableRel (onsTorusAdj L) := by
  intro u v; unfold onsTorusAdj; infer_instance

def onsTorusGraph (L : ℕ) [Fact (2 < L)] : SimpleGraph (ZMod L × ZMod L) where
  Adj := onsTorusAdj L
  symm := by
    rintro u v (⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩)
    · exact Or.inl ⟨h1.symm, Or.inr (by rw [h2]; ring)⟩
    · exact Or.inl ⟨h1.symm, Or.inl (by rw [h2]; ring)⟩
    · exact Or.inr ⟨h1.symm, Or.inr (by rw [h2]; ring)⟩
    · exact Or.inr ⟨h1.symm, Or.inl (by rw [h2]; ring)⟩
  loopless := by
    have hne1 : (1 : ZMod L) ≠ 0 := by
      have : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
      exact one_ne_zero
    have hnem1 : (-1 : ZMod L) ≠ 0 := neg_ne_zero.mpr hne1
    refine ⟨?_⟩
    rintro v (⟨_, h2 | h2⟩ | ⟨_, h2 | h2⟩)
    · exact hne1 (by linear_combination -h2)
    · exact hnem1 (by linear_combination -h2)
    · exact hne1 (by linear_combination -h2)
    · exact hnem1 (by linear_combination -h2)

instance instNeZeroOfFact (L : ℕ) [Fact (2 < L)] : NeZero L :=
  ⟨by have := (Fact.out : 2 < L); omega⟩

instance (L : ℕ) [Fact (2 < L)] : DecidableRel (onsTorusGraph L).Adj :=
  inferInstanceAs (DecidableRel (onsTorusAdj L))

theorem onsTorus_card_verts (L : ℕ) [NeZero L] :
    Fintype.card (ZMod L × ZMod L) = L ^ 2 := by
  rw [Fintype.card_prod, ZMod.card]; ring

theorem onsTorus_degree (L : ℕ) [Fact (2 < L)] (v : ZMod L × ZMod L) :
    (onsTorusGraph L).degree v = 4 := by
  have h1 : (1 : ZMod L) ≠ 0 := by
    rw [Ne, ← Nat.cast_one, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    have := (Fact.out : 2 < L); omega
  have h2 : (2 : ZMod L) ≠ 0 := by
    have : ((2 : ℕ) : ZMod L) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      have := (Fact.out : 2 < L); omega
    simpa using this
  
  set A : ZMod L × ZMod L := (v.1, v.2 - 1) with hA_def
  set B : ZMod L × ZMod L := (v.1, v.2 + 1) with hB_def
  set C : ZMod L × ZMod L := (v.1 - 1, v.2) with hC_def
  set D : ZMod L × ZMod L := (v.1 + 1, v.2) with hD_def
  have hAB : A ≠ B := by
    intro h; rw [Prod.ext_iff] at h; exact h2 (by linear_combination -h.2)
  have hAC : A ≠ C := by
    intro h; rw [Prod.ext_iff] at h; exact h1 (by linear_combination h.1)
  have hAD : A ≠ D := by
    intro h; rw [Prod.ext_iff] at h; exact h1 (by linear_combination -h.1)
  have hBC : B ≠ C := by
    intro h; rw [Prod.ext_iff] at h; exact h1 (by linear_combination h.1)
  have hBD : B ≠ D := by
    intro h; rw [Prod.ext_iff] at h; exact h1 (by linear_combination -h.1)
  have hCD : C ≠ D := by
    intro h; rw [Prod.ext_iff] at h; exact h2 (by linear_combination -h.1)
  have hset : (onsTorusGraph L).neighborFinset v = {A, B, C, D} := by
    ext w
    rw [SimpleGraph.mem_neighborFinset]
    simp only [Finset.mem_insert, Finset.mem_singleton, hA_def, hB_def, hC_def, hD_def]
    constructor
    · rintro (⟨g1, g2 | g2⟩ | ⟨g1, g2 | g2⟩)
      · exact Or.inl (Prod.ext_iff.mpr ⟨g1.symm, by linear_combination -g2⟩)
      · exact Or.inr (Or.inl (Prod.ext_iff.mpr ⟨g1.symm, by linear_combination -g2⟩))
      · exact Or.inr (Or.inr (Or.inl (Prod.ext_iff.mpr ⟨by linear_combination -g2, g1.symm⟩)))
      · exact Or.inr (Or.inr (Or.inr (Prod.ext_iff.mpr ⟨by linear_combination -g2, g1.symm⟩)))
    · rintro (rfl | rfl | rfl | rfl)
      · exact Or.inl ⟨rfl, Or.inl (by ring)⟩
      · exact Or.inl ⟨rfl, Or.inr (by ring)⟩
      · exact Or.inr ⟨rfl, Or.inl (by ring)⟩
      · exact Or.inr ⟨rfl, Or.inr (by ring)⟩
  change Finset.card ((onsTorusGraph L).neighborFinset v) = 4
  rw [hset]
  rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hAB, hAC, hAD⟩),
      Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hBC, hBD⟩),
      Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact hCD),
      Finset.card_singleton]

theorem onsTorus_card_edges (L : ℕ) [Fact (2 < L)] :
    (onsTorusGraph L).edgeFinset.card = 2 * L ^ 2 := by
  have hsum := (onsTorusGraph L).sum_degrees_eq_twice_card_edges
  have hdeg : ∀ v, (onsTorusGraph L).degree v = 4 := onsTorus_degree L
  simp only [hdeg, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  rw [onsTorus_card_verts] at hsum
  omega

end StatMech.Onsager
