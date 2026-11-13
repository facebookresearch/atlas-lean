/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Abel

@[expose] public section

section
open scoped Pointwise

namespace MetaMathlibExt

private theorem card_add_le_card_sub_of_symm {α : Type*} [AddCommGroup α] [DecidableEq α]
    (A : Finset α) (s : α) (h : ∀ x ∈ A, s - x ∈ A) :
    (A + A).card ≤ (A - A).card := by
  have hsub : A + A ⊆ {s} + (A - A) := by
    intro z hz
    rw [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    have hsy : s - y ∈ A := h y hy
    have hmem : x - (s - y) ∈ A - A := Finset.sub_mem_sub hx hsy
    rw [Finset.mem_add]
    exact ⟨s, by simp, x - (s - y), hmem, by abel⟩
  calc (A + A).card ≤ ({s} + (A - A)).card := Finset.card_le_card hsub
    _ = (A - A).card := Finset.card_singleton_add s (A - A)

private theorem card_add_le_card_sub_of_certificate (A : Finset ℤ) (S P : List ℤ)
    (hne : A.Nonempty) (hS : ∀ x ∈ A, ∀ y ∈ A, x + y ∈ S)
    (hP : ∀ p ∈ P, 0 < p ∧ p ∈ A - A) (hPn : P.Nodup)
    (hlen : S.length ≤ 2 * P.length + 1) :
    (A + A).card ≤ (A - A).card := by
  obtain ⟨x0, hx0⟩ := hne
  have h0 : (0 : ℤ) ∈ A - A := by
    have h := Finset.sub_mem_sub hx0 hx0
    simpa using h
  have hsub : A + A ⊆ S.toFinset := by
    intro z hz
    rw [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    rw [List.mem_toFinset]
    exact hS x hx y hy
  have hub : (A + A).card ≤ S.length :=
    le_trans (Finset.card_le_card hsub) (List.toFinset_card_le S)
  have hLmem : ∀ q ∈ (0 :: (P ++ P.map (fun p => -p))), q ∈ A - A := by
    intro q hq
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hq
    rcases hq with rfl | hPmem | ⟨p, hpP, rfl⟩
    · exact h0
    · exact (hP _ hPmem).2
    · obtain ⟨hpos, hmem⟩ := hP p hpP
      rw [Finset.mem_sub] at hmem ⊢
      obtain ⟨u, hu, v, hv, huv⟩ := hmem
      exact ⟨v, hv, u, hu, by omega⟩
  have h0not : (0 : ℤ) ∉ P ++ P.map (fun p => -p) := by
    simp only [List.mem_append, List.mem_map]
    rintro (hP0 | ⟨p, hpP, hneg⟩)
    · exact absurd (hP _ hP0).1 (by omega)
    · have hpos := (hP p hpP).1
      omega
  have hmapnodup : (P.map (fun p : ℤ => -p)).Nodup :=
    List.Nodup.map (fun a b hab => neg_injective hab) hPn
  have hdisj : ∀ a ∈ P, ∀ b ∈ P.map (fun p : ℤ => -p), a ≠ b := by
    intro q hq1 b hq2
    rw [List.mem_map] at hq2
    obtain ⟨p, hpP, hpq⟩ := hq2
    have hpos1 := (hP q hq1).1
    have hpos2 := (hP p hpP).1
    omega
  have hLnodup : (0 :: (P ++ P.map (fun p : ℤ => -p))).Nodup :=
    List.nodup_cons.mpr ⟨h0not, List.nodup_append.mpr ⟨hPn, hmapnodup, hdisj⟩⟩
  have hLcard : (0 :: (P ++ P.map (fun p : ℤ => -p))).toFinset.card
      = (0 :: (P ++ P.map (fun p : ℤ => -p))).length :=
    List.toFinset_card_of_nodup hLnodup
  have hLsub : (0 :: (P ++ P.map (fun p : ℤ => -p))).toFinset ⊆ A - A := by
    intro q hq
    rw [List.mem_toFinset] at hq
    exact hLmem q hq
  have hlb : (0 :: (P ++ P.map (fun p : ℤ => -p))).length ≤ (A - A).card := by
    have h := Finset.card_le_card hLsub
    rwa [hLcard] at h
  simp only [List.length_cons, List.length_append, List.length_map] at hlb
  omega

private theorem exists_sorted_of_card_eq_three (A : Finset ℤ) (h : A.card = 3) :
    ∃ a b c : ℤ, a < b ∧ b < c ∧ A = {a, b, c} := by
  let f := A.orderEmbOfFin h
  refine ⟨f 0, f 1, f 2, ?_, ?_, ?_⟩
  · exact f.strictMono (by decide)
  · exact f.strictMono (by decide)
  · have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
    have himg := Finset.image_orderEmbOfFin_univ A h
    rw [huniv, Finset.image_insert, Finset.image_insert, Finset.image_singleton] at himg
    rw [← himg]

private theorem exists_sorted_of_card_eq_four (A : Finset ℤ) (h : A.card = 4) :
    ∃ a b c d : ℤ, a < b ∧ b < c ∧ c < d ∧ A = {a, b, c, d} := by
  let f := A.orderEmbOfFin h
  refine ⟨f 0, f 1, f 2, f 3, ?_, ?_, ?_, ?_⟩
  · exact f.strictMono (by decide)
  · exact f.strictMono (by decide)
  · exact f.strictMono (by decide)
  · have huniv : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
    have himg := Finset.image_orderEmbOfFin_univ A h
    rw [huniv, Finset.image_insert, Finset.image_insert, Finset.image_insert,
      Finset.image_singleton] at himg
    rw [← himg]

private theorem exists_sorted_of_card_eq_five (A : Finset ℤ) (h : A.card = 5) :
    ∃ a b c d e : ℤ, a < b ∧ b < c ∧ c < d ∧ d < e ∧ A = {a, b, c, d, e} := by
  let f := A.orderEmbOfFin h
  refine ⟨f 0, f 1, f 2, f 3, f 4, ?_, ?_, ?_, ?_, ?_⟩
  · exact f.strictMono (by decide)
  · exact f.strictMono (by decide)
  · exact f.strictMono (by decide)
  · exact f.strictMono (by decide)
  · have huniv : (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} := by decide
    have himg := Finset.image_orderEmbOfFin_univ A h
    rw [huniv, Finset.image_insert, Finset.image_insert, Finset.image_insert,
      Finset.image_insert, Finset.image_singleton] at himg
    rw [← himg]

private theorem nssd_card_three_symm (a b c : ℤ) (_hab : a < b) (hbc : b < c)
    (hsym : a + c = 2 * b) :
    (({a, b, c} : Finset ℤ) + {a, b, c}).card ≤ (({a, b, c} : Finset ℤ) - {a, b, c}).card := by
  apply card_add_le_card_sub_of_symm _ (a + c)
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

private theorem nssd_three_ac_ne_two_b (a b c : ℤ) (hab : a < b) (hbc : b < c)
    (hne : a + c ≠ 2 * b)
    : (({a, b, c} : Finset ℤ) + {a, b, c}).card ≤ (({a, b, c} : Finset ℤ) - {a, b, c}).card := by
  apply card_add_le_card_sub_of_certificate _ [2 * a, a + b, a + c, 2 * b, b + c, 2 * c]
      [b - a, c - b, c - a]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_card_le_three (A : Finset ℤ) (h : A.card ≤ 3) :
    (A + A).card ≤ (A - A).card := by
  have h03 : A.card = 0 ∨ A.card = 1 ∨ A.card = 2 ∨ A.card = 3 := by omega
  rcases h03 with h0 | h1 | h2 | h3
  · rw [Finset.card_eq_zero.mp h0]
    simp
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
    rw [hx]
    apply card_add_le_card_sub_of_symm _ (2 * x)
    intro y hy
    simp only [Finset.mem_singleton] at hy
    simp only [Finset.mem_singleton]
    omega
  · obtain ⟨x, y, hxy, hx⟩ := Finset.card_eq_two.mp h2
    rw [hx]
    apply card_add_le_card_sub_of_symm _ (x + y)
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · obtain ⟨a, b, c, hab, hbc, rfl⟩ := exists_sorted_of_card_eq_three A h3
    by_cases hsym : a + c = 2 * b
    · exact nssd_card_three_symm a b c hab hbc hsym
    · exact nssd_three_ac_ne_two_b a b c hab hbc hsym

private theorem nssd_four_ae_eq_two_b (a b c d : ℤ) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (_h1 : a + d ≠ b + c)
    (h2 : a + d = 2 * b)
    : (({a, b, c, d} : Finset ℤ) + {a, b, c, d}).card ≤
        (({a, b, c, d} : Finset ℤ) - {a, b, c, d}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, a + c, 2 * b, b + c, b + d, 2 * c, c + d, 2 * d] [c - b, c - a, d - b, d - a]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_four_ac_eq_two_b (a b c d : ℤ) (_hab : a < b) (hbc : b < c) (hcd : c < d)
    (h1 : a + d ≠ b + c)
    (hn2 : a + d ≠ 2 * b)
    (h3 : a + c = 2 * b)
    : (({a, b, c, d} : Finset ℤ) + {a, b, c, d}).card ≤
        (({a, b, c, d} : Finset ℤ) - {a, b, c, d}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, a + d, 2 * b, b + c, b + d, 2 * c, c + d, 2 * d] [c - b, c - a, d - b, d - a]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_four_rest (a b c d : ℤ) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (h1 : a + d ≠ b + c)
    (hn2 : a + d ≠ 2 * b)
    (hn3 : a + c ≠ 2 * b)
    : (({a, b, c, d} : Finset ℤ) + {a, b, c, d}).card ≤
        (({a, b, c, d} : Finset ℤ) - {a, b, c, d}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, a + c, a + d, 2 * b, b + c, b + d, 2 * c, c + d, 2 * d]
          [b - a, c - b, c - a, d - b, d - a]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_card_four (a b c d : ℤ) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    (({a, b, c, d} : Finset ℤ) + {a, b, c, d}).card ≤
      (({a, b, c, d} : Finset ℤ) - {a, b, c, d}).card := by
  by_cases h1 : a + d = b + c
  · apply card_add_le_card_sub_of_symm _ (a + d)
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · by_cases h2 : a + d = 2 * b
    · exact nssd_four_ae_eq_two_b a b c d hab hbc hcd h1 h2
    · by_cases h3 : a + c = 2 * b
      · exact nssd_four_ac_eq_two_b a b c d hab hbc hcd h1 h2 h3
      · exact nssd_four_rest a b c d hab hbc hcd h1 h2 h3

private theorem nssd_five_generic (a b c d e : ℤ) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hde : d < e)
    (hg1 : a + e ≠ 2 * b)
    (hg2 : a + e ≠ b + c)
    (hg3 : a + e ≠ 2 * c)
    (hg4 : a + e ≠ b + d)
    (hg5 : a + e ≠ c + d)
    (hg6 : a + e ≠ 2 * d)
    : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, a + c, a + d, a + e, 2 * b, b + c, b + d, b + e, 2 * c, c + d, c + e, 2 * d, d
          + e, 2 * e] [b - a, c - a, d - a, e - a, e - b, e - c, e - d]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_five_ae_eq_two_b_bd_eq_two_c (a b c d e : ℤ) (hab : a < b) (hbc : b < c)
    (_hcd : c < d) (hde : d < e)
    (h7 : a + e = 2 * b)
    (hb : b + d = 2 * c)
    : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, a + c, a + d, 2 * b, b + c, b + e, 2 * c, c + d, c + e, 2 * d, d + e, 2 * e]
          [b - a, c - a, d - a, e - a, c - b, d - b]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_five_ae_eq_two_b_bd_ne_two_c (a b c d e : ℤ) (hab : a < b) (hbc : b < c)
    (hcd : c < d) (hde : d < e)
    (h7 : a + e = 2 * b)
    (hb : b + d ≠ 2 * c)
    : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, a + c, a + d, 2 * b, b + c, b + d, b + e, 2 * c, c + d, c + e, 2 * d, d + e, 2
          * e] [b - a, c - a, d - a, e - a, c - b, d - b, d - c]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_five_ae_eq_two_d_ac_eq_two_b (a b c d e : ℤ) (_hab : a < b) (hbc : b < c)
    (hcd : c < d) (hde : d < e)
    (h8 : a + e = 2 * d)
    (ha : a + c = 2 * b)
    : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, a + d, 2 * b, b + c, b + d, b + e, 2 * c, c + d, c + e, 2 * d, d + e, 2 * e]
          [b - a, c - a, d - a, e - a, e - b, e - c]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_five_ae_eq_two_d_ac_ne_two_b (a b c d e : ℤ) (hab : a < b) (hbc : b < c)
    (hcd : c < d) (hde : d < e)
    (h8 : a + e = 2 * d)
    (ha : a + c ≠ 2 * b)
    : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, a + c, a + d, 2 * b, b + c, b + d, b + e, 2 * c, c + d, c + e, 2 * d, d + e, 2
          * e] [b - a, c - a, d - a, e - a, c - b, e - b, e - c]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_five_ae_eq_two_c_ad_eq_bc (a b c d e : ℤ) (hab : a < b) (hbc : b < c)
    (hcd : c < d) (_hde : d < e)
    (h9 : a + e = 2 * c)
    (hne : a + e ≠ b + d)
    (had : a + d = b + c)
    : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, a + c, 2 * b, b + c, b + d, 2 * c, c + d, c + e, 2 * d, d + e, 2 * e]
          [b - a, c - a, d - a, e - a, c - b, e - b]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_five_ae_eq_two_c_ad_ne_bc (a b c d e : ℤ) (hab : a < b) (hbc : b < c)
    (hcd : c < d) (hde : d < e)
    (h9 : a + e = 2 * c)
    (hne : a + e ≠ b + d)
    (had : a + d ≠ b + c)
    : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, a + c, a + d, 2 * b, b + c, b + d, b + e, 2 * c, c + d, c + e, 2 * d, d + e, 2
          * e] [c - a, d - a, e - a, c - b, d - b, e - b, d - c]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_five_ae_eq_bc_ac_eq_two_b (a b c d e : ℤ) (_hab : a < b) (hbc : b < c)
    (hcd : c < d) (hde : d < e)
    (h10 : a + e = b + c)
    (h1 : a + c = 2 * b)
    : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, a + d, 2 * b, b + c, b + d, 2 * c, c + d, c + e, 2 * d, d + e, 2 * e]
          [b - a, c - a, d - a, e - a, d - b, d - c]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_five_ae_eq_bc_ad_two_b_bd_two_c (a b c d e : ℤ) (_hab : a < b) (_hbc : b < c)
    (_hcd : c < d) (hde : d < e)
    (h10 : a + e = b + c)
    (_hn1 : a + c ≠ 2 * b)
    (h2 : a + d = 2 * b)
    (h3 : b + d = 2 * c)
    : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, a + c, 2 * b, b + c, 2 * c, c + d, 2 * d, d + e, 2 * e]
          [b - a, c - a, d - a, e - a, c - b]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_five_ae_eq_bc_ad_two_b_bd_ne (a b c d e : ℤ) (hab : a < b) (_hbc : b < c)
    (hcd : c < d) (hde : d < e)
    (h10 : a + e = b + c)
    (_hn1 : a + c ≠ 2 * b)
    (h2 : a + d = 2 * b)
    (hn3 : b + d ≠ 2 * c)
    : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, a + c, 2 * b, b + c, b + d, 2 * c, c + d, c + e, 2 * d, d + e, 2 * e]
          [b - a, c - a, d - a, e - a, c - b, d - c]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_five_ae_eq_bc_ad_ne_bd_two_c (a b c d e : ℤ) (hab : a < b) (hbc : b < c)
    (hcd : c < d) (hde : d < e)
    (h10 : a + e = b + c)
    (_hn1 : a + c ≠ 2 * b)
    (hn2 : a + d ≠ 2 * b)
    (h4 : b + d = 2 * c)
    : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, a + c, a + d, 2 * b, b + c, b + e, 2 * c, c + d, c + e, 2 * d, d + e, 2 * e]
          [b - a, c - a, d - a, e - a, c - b, d - b]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_five_ae_eq_bc_rest (a b c d e : ℤ) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hde : d < e)
    (h10 : a + e = b + c)
    (hn1 : a + c ≠ 2 * b)
    (hn2 : a + d ≠ 2 * b)
    (hn4 : b + d ≠ 2 * c)
    : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, a + c, a + d, 2 * b, b + c, b + d, b + e, 2 * c, c + d, c + e, 2 * d, d + e, 2
          * e] [b - a, c - a, d - a, e - a, c - b, d - b, d - c]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_five_ae_eq_cd_ac_two_b_ad_bc (a b c d e : ℤ) (_hab : a < b) (hbc : b < c)
    (_hcd : c < d) (hde : d < e)
    (h11 : a + e = c + d)
    (h1 : a + c = 2 * b)
    (h2 : a + d = b + c)
    : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, 2 * b, b + c, 2 * c, c + d, c + e, 2 * d, d + e, 2 * e]
          [b - a, c - a, d - a, e - a, e - b]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_five_ae_eq_cd_ac_two_b_ad_ne (a b c d e : ℤ) (_hab : a < b) (hbc : b < c)
    (hcd : c < d) (hde : d < e)
    (h11 : a + e = c + d)
    (h1 : a + c = 2 * b)
    (hn2 : a + d ≠ b + c)
    : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, a + d, 2 * b, b + c, b + d, b + e, 2 * c, c + d, c + e, 2 * d, d + e, 2 * e]
          [b - a, c - a, d - a, e - a, d - b, e - b]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_five_ae_eq_cd_ac_ne_ad_two_b (a b c d e : ℤ) (hab : a < b) (hbc : b < c)
    (hcd : c < d) (hde : d < e)
    (h11 : a + e = c + d)
    (_hn1 : a + c ≠ 2 * b)
    (h3 : a + d = 2 * b)
    : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, a + c, 2 * b, b + c, b + d, b + e, 2 * c, c + d, c + e, 2 * d, d + e, 2 * e]
          [b - a, c - a, d - a, e - a, c - b, e - b]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_five_ae_eq_cd_ac_ne_ad_ne_ad_bc (a b c d e : ℤ) (hab : a < b) (hbc : b < c)
    (hcd : c < d) (hde : d < e)
    (h11 : a + e = c + d)
    (hn1 : a + c ≠ 2 * b)
    (hn3 : a + d ≠ 2 * b)
    (h4 : a + d = b + c)
    : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, a + c, 2 * b, b + c, b + d, 2 * c, c + d, c + e, 2 * d, d + e, 2 * e]
          [b - a, c - a, d - a, e - a, c - b, e - b]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_five_ae_eq_cd_rest (a b c d e : ℤ) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hde : d < e)
    (h11 : a + e = c + d)
    (hn1 : a + c ≠ 2 * b)
    (hn3 : a + d ≠ 2 * b)
    (hn4 : a + d ≠ b + c)
    : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, a + c, a + d, 2 * b, b + c, b + d, b + e, 2 * c, c + d, c + e, 2 * d, d + e, 2
          * e] [b - a, c - a, d - a, e - a, c - b, d - b, e - b]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_five_ae_eq_bd_ac_two_b_ad_two_c (a b c d e : ℤ) (_hab : a < b) (_hbc : b < c)
    (_hcd : c < d) (hde : d < e)
    (h12 : a + e = b + d)
    (_hne : a + e ≠ 2 * c)
    (h1 : a + c = 2 * b)
    (h2 : a + d = 2 * c)
    : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, 2 * b, b + c, b + d, 2 * c, c + d, c + e, 2 * d, d + e, 2 * e]
          [b - a, c - a, d - a, e - a, d - b]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_five_ae_eq_bd_ac_two_b_ad_ne (a b c d e : ℤ) (_hab : a < b) (_hbc : b < c)
    (hcd : c < d) (hde : d < e)
    (h12 : a + e = b + d)
    (hne : a + e ≠ 2 * c)
    (h1 : a + c = 2 * b)
    (hn2 : a + d ≠ 2 * c)
    : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, a + d, 2 * b, b + c, b + d, 2 * c, c + d, c + e, 2 * d, d + e, 2 * e]
          [b - a, c - a, d - a, e - a, d - b, d - c]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_five_ae_eq_bd_ad_two_b (a b c d e : ℤ) (_hab : a < b) (hbc : b < c)
    (hcd : c < d) (hde : d < e)
    (h12 : a + e = b + d)
    (hne : a + e ≠ 2 * c)
    (hn1 : a + c ≠ 2 * b)
    (h3 : a + d = 2 * b)
    : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, a + c, 2 * b, b + c, b + d, 2 * c, c + d, c + e, 2 * d, d + e, 2 * e]
          [b - a, c - a, d - a, e - a, c - b, d - c]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_five_ae_eq_bd_ntb_ad_bc_be_two_c (a b c d e : ℤ) (_hab : a < b) (hbc : b < c)
    (_hcd : c < d) (_hde : d < e)
    (h13 : a + e = b + d)
    (_hne : a + e ≠ 2 * c)
    (_hn1 : a + c ≠ 2 * b)
    (_hn2 : a + d ≠ 2 * b)
    (h1 : a + d = b + c)
    (h2 : b + e = 2 * c)
    : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, a + c, 2 * b, b + c, b + d, 2 * c, c + d, 2 * d, d + e, 2 * e]
          [b - a, c - a, d - a, e - a, c - b]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_five_ae_eq_bd_ntb_ad_bc_be_ne (a b c d e : ℤ) (_hab : a < b) (hbc : b < c)
    (_hcd : c < d) (hde : d < e)
    (h13 : a + e = b + d)
    (_hne : a + e ≠ 2 * c)
    (hn1 : a + c ≠ 2 * b)
    (hn2 : a + d ≠ 2 * b)
    (h1 : a + d = b + c)
    (hn2b : b + e ≠ 2 * c)
    : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, a + c, 2 * b, b + c, b + d, b + e, 2 * c, c + d, 2 * d, d + e, 2 * e]
          [b - a, c - a, d - a, e - a, c - b, e - c]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_five_ae_eq_bd_ntb_ad_two_c (a b c d e : ℤ) (_hab : a < b) (hbc : b < c)
    (hcd : c < d) (hde : d < e)
    (h13 : a + e = b + d)
    (_hne : a + e ≠ 2 * c)
    (hn1 : a + c ≠ 2 * b)
    (hn2 : a + d ≠ 2 * b)
    (hn1b : a + d ≠ b + c)
    (h3 : a + d = 2 * c)
    : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, a + c, 2 * b, b + c, b + d, b + e, 2 * c, c + d, c + e, 2 * d, d + e, 2 * e]
          [b - a, c - a, d - a, e - a, c - b, d - b]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_five_ae_eq_bd_ntb_rest (a b c d e : ℤ) (_hab : a < b) (hbc : b < c)
    (hcd : c < d) (hde : d < e)
    (h13 : a + e = b + d)
    (hne : a + e ≠ 2 * c)
    (hn1 : a + c ≠ 2 * b)
    (hn2 : a + d ≠ 2 * b)
    (hn1b : a + d ≠ b + c)
    (hn3 : a + d ≠ 2 * c)
    : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  apply card_add_le_card_sub_of_certificate _
      [2 * a, a + b, a + c, a + d, 2 * b, b + c, b + d, b + e, 2 * c, c + d, c + e, 2 * d, d + e, 2
          * e] [b - a, c - a, d - a, e - a, c - b, d - b, d - c]
  · exact Finset.insert_nonempty _ _
  · intro x hx y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
    · exact ⟨by omega, Finset.sub_mem_sub (by simp) (by simp)⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, not_false_eq_true, and_true]
    omega
  · simp

private theorem nssd_five_ae_eq_two_b (a b c d e : ℤ) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hde : d < e)
    (h7 : a + e = 2 * b) : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  by_cases hb : b + d = 2 * c
  · exact nssd_five_ae_eq_two_b_bd_eq_two_c a b c d e hab hbc hcd hde h7 hb
  · exact nssd_five_ae_eq_two_b_bd_ne_two_c a b c d e hab hbc hcd hde h7 hb

private theorem nssd_five_ae_eq_two_d (a b c d e : ℤ) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hde : d < e)
    (h8 : a + e = 2 * d) : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  by_cases ha : a + c = 2 * b
  · exact nssd_five_ae_eq_two_d_ac_eq_two_b a b c d e hab hbc hcd hde h8 ha
  · exact nssd_five_ae_eq_two_d_ac_ne_two_b a b c d e hab hbc hcd hde h8 ha

private theorem nssd_five_ae_eq_two_c (a b c d e : ℤ) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hde : d < e)
    (h9 : a + e = 2 * c) (hne : a + e ≠ b + d) :
        (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
            (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  by_cases had : a + d = b + c
  · exact nssd_five_ae_eq_two_c_ad_eq_bc a b c d e hab hbc hcd hde h9 hne had
  · exact nssd_five_ae_eq_two_c_ad_ne_bc a b c d e hab hbc hcd hde h9 hne had

private theorem nssd_five_ae_eq_bc (a b c d e : ℤ) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hde : d < e)
    (h10 : a + e = b + c) : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  by_cases h1 : a + c = 2 * b
  · exact nssd_five_ae_eq_bc_ac_eq_two_b a b c d e hab hbc hcd hde h10 h1
  · by_cases h2 : a + d = 2 * b
    · by_cases h3 : b + d = 2 * c
      · exact nssd_five_ae_eq_bc_ad_two_b_bd_two_c a b c d e hab hbc hcd hde h10 h1 h2 h3
      · exact nssd_five_ae_eq_bc_ad_two_b_bd_ne a b c d e hab hbc hcd hde h10 h1 h2 h3
    · by_cases h4 : b + d = 2 * c
      · exact nssd_five_ae_eq_bc_ad_ne_bd_two_c a b c d e hab hbc hcd hde h10 h1 h2 h4
      · exact nssd_five_ae_eq_bc_rest a b c d e hab hbc hcd hde h10 h1 h2 h4

private theorem nssd_five_ae_eq_cd (a b c d e : ℤ) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hde : d < e)
    (h11 : a + e = c + d) : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  by_cases h1 : a + c = 2 * b
  · by_cases h2 : a + d = b + c
    · exact nssd_five_ae_eq_cd_ac_two_b_ad_bc a b c d e hab hbc hcd hde h11 h1 h2
    · exact nssd_five_ae_eq_cd_ac_two_b_ad_ne a b c d e hab hbc hcd hde h11 h1 h2
  · by_cases h3 : a + d = 2 * b
    · exact nssd_five_ae_eq_cd_ac_ne_ad_two_b a b c d e hab hbc hcd hde h11 h1 h3
    · by_cases h4 : a + d = b + c
      · exact nssd_five_ae_eq_cd_ac_ne_ad_ne_ad_bc a b c d e hab hbc hcd hde h11 h1 h3 h4
      · exact nssd_five_ae_eq_cd_rest a b c d e hab hbc hcd hde h11 h1 h3 h4

private theorem nssd_five_ae_eq_bd_of_two_b (a b c d e : ℤ) (hab : a < b) (hbc : b < c)
    (hcd : c < d) (hde : d < e)
    (h12 : a + e = b + d) (hne : a + e ≠ 2 * c)
    (hor : a + c = 2 * b ∨ a + d = 2 * b) : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  by_cases h1 : a + c = 2 * b ∧ a + d = 2 * c
  · exact nssd_five_ae_eq_bd_ac_two_b_ad_two_c a b c d e hab hbc hcd hde h12 hne h1.1 h1.2
  · by_cases h2 : a + c = 2 * b
    · exact nssd_five_ae_eq_bd_ac_two_b_ad_ne a b c d e hab hbc hcd hde h12 hne h2
        (fun he => h1 ⟨h2, he⟩)
    · have h3 : a + d = 2 * b := by
        rcases hor with h | h
        · exact absurd h h2
        · exact h
      exact nssd_five_ae_eq_bd_ad_two_b a b c d e hab hbc hcd hde h12 hne h2 h3

private theorem nssd_five_ae_eq_bd_of_not_two_b (a b c d e : ℤ) (hab : a < b) (hbc : b < c)
    (hcd : c < d) (hde : d < e)
    (h13 : a + e = b + d) (hne : a + e ≠ 2 * c)
    (hn1 : a + c ≠ 2 * b) (hn2 : a + d ≠ 2 * b) :
        (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
            (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  by_cases h1 : a + d = b + c ∧ b + e = 2 * c
  · exact nssd_five_ae_eq_bd_ntb_ad_bc_be_two_c a b c d e hab hbc hcd hde h13 hne hn1 hn2
      h1.1 h1.2
  · by_cases h2 : a + d = b + c
    · exact nssd_five_ae_eq_bd_ntb_ad_bc_be_ne a b c d e hab hbc hcd hde h13 hne hn1 hn2
        h2 (fun he => h1 ⟨h2, he⟩)
    · by_cases h3 : a + d = 2 * c
      · exact nssd_five_ae_eq_bd_ntb_ad_two_c a b c d e hab hbc hcd hde h13 hne hn1 hn2
          h2 h3
      · exact nssd_five_ae_eq_bd_ntb_rest a b c d e hab hbc hcd hde h13 hne hn1 hn2
          h2 h3

private theorem nssd_card_five (a b c d e : ℤ) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hde : d < e) : (({a, b, c, d, e} : Finset ℤ) + {a, b, c, d, e}).card ≤
        (({a, b, c, d, e} : Finset ℤ) - {a, b, c, d, e}).card := by
  by_cases hsym : a + e = 2 * c ∧ a + e = b + d
  · apply card_add_le_card_sub_of_symm _ (a + e)
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  · by_cases h7 : a + e = 2 * b
    · exact nssd_five_ae_eq_two_b a b c d e hab hbc hcd hde h7
    · by_cases h8 : a + e = 2 * d
      · exact nssd_five_ae_eq_two_d a b c d e hab hbc hcd hde h8
      · by_cases h9 : a + e = 2 * c
        · have hne : a + e ≠ b + d := fun he => hsym ⟨h9, he⟩
          exact nssd_five_ae_eq_two_c a b c d e hab hbc hcd hde h9 hne
        · by_cases h10 : a + e = b + c
          · exact nssd_five_ae_eq_bc a b c d e hab hbc hcd hde h10
          · by_cases h11 : a + e = c + d
            · exact nssd_five_ae_eq_cd a b c d e hab hbc hcd hde h11
            · by_cases h12 : a + e = b + d
              · have hne : a + e ≠ 2 * c := h9
                by_cases hor : a + c = 2 * b ∨ a + d = 2 * b
                · exact nssd_five_ae_eq_bd_of_two_b a b c d e hab hbc hcd hde h12 hne hor
                · have hn1 : a + c ≠ 2 * b := fun he => hor (Or.inl he)
                  have hn2 : a + d ≠ 2 * b := fun he => hor (Or.inr he)
                  exact nssd_five_ae_eq_bd_of_not_two_b a b c d e hab hbc hcd hde h12 hne
                    hn1 hn2
              · exact nssd_five_generic a b c d e hab hbc hcd hde h7 h10 h9 h12 h11 h8

/--
**Chu's theorem for arbitrary finite sets of integers.** Let $A$ be a finite set of integers with
$|A| < 6$. Then $|A + A| \le |A - A|$, where $A + A = \{a + b : a, b \in A\}$ is the sumset and
$A - A = \{a - b : a, b \in A\}$ is the difference set of $A$.

This is Chu's theorem without the assumption that the elements of $A$ are nonnegative.
-/
theorem card_add_le_card_sub_of_card_lt_six (A : Finset ℤ) (h_card : A.card < 6) :
    (A + A).card ≤ (A - A).card := by
  have h56 : A.card ≤ 3 ∨ A.card = 4 ∨ A.card = 5 := by omega
  rcases h56 with h | h | h
  · exact nssd_card_le_three A h
  · obtain ⟨a, b, c, d, hab, hbc, hcd, rfl⟩ := exists_sorted_of_card_eq_four A h
    exact nssd_card_four a b c d hab hbc hcd
  · obtain ⟨a, b, c, d, e, hab, hbc, hcd, hde, rfl⟩ := exists_sorted_of_card_eq_five A h
    exact nssd_card_five a b c d e hab hbc hcd hde

/--
**Chu's theorem: sets with fewer than six elements are not sum-dominant.** Let $A$ be a finite
set of nonnegative integers with $|A| < 6$. Then $|A + A| \le |A - A|$, where
$A + A = \{a + b : a, b \in A\}$ is the sumset and $A - A = \{a - b : a, b \in A\}$ is the
difference set of $A$; that is, $A$ is not sum-dominant.

The nonnegativity assumption follows the source's normalization and is not needed: the same
bound holds for every finite set of integers with fewer than six elements.

Proves `Wanted` entry `no_small_sum_dominant`.

Source: Hùng Việt Chu, "When Sets Are Not Sum-Dominant," Journal of Integer
Sequences 22 (2019), Article 19.3.7, Theorem (label notsum-dominant),
lines 126–128,
https://cs.uwaterloo.ca/journals/JIS/VOL22/Chu/chu5.tex
-/
theorem no_small_sum_dominant :
    ∀ (A : Finset ℤ) (h_nonneg : ∀ x ∈ A, 0 ≤ x) (h_card : A.card < 6),
      (A + A).card ≤ (A - A).card :=
  fun A _ h_card => card_add_le_card_sub_of_card_lt_six A h_card

end MetaMathlibExt
end
