/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































import Mathlib
import Code.Lattice.HypercubicLattice

open Set
open SimpleGraph

namespace StatMech

namespace Lattice





theorem sw_adj_horizSucc (y x : ℤ) :
    (hypercubicLattice 2).Adj ![x, y] ![x + 1, y] := by
  rw [hypercubicLattice_adj]; simp [Fin.sum_univ_two]



theorem sw_adj_vertSucc (x y : ℤ) :
    (hypercubicLattice 2).Adj ![x, y] ![x, y + 1] := by
  rw [hypercubicLattice_adj]; simp [Fin.sum_univ_two]





def sw_horizR (y x0 : ℤ) :
    (n : ℕ) → (hypercubicLattice 2).Walk ![x0, y] ![x0 + (n : ℤ), y]
  | 0 => Walk.nil.copy rfl (by norm_num)
  | (n + 1) =>
      (sw_horizR y x0 n).append
        ((Walk.cons (sw_adj_horizSucc y (x0 + (n : ℤ))) Walk.nil).copy rfl
          (by norm_num [add_assoc]))


def sw_vertU (x y0 : ℤ) :
    (n : ℕ) → (hypercubicLattice 2).Walk ![x, y0] ![x, y0 + (n : ℤ)]
  | 0 => Walk.nil.copy rfl (by norm_num)
  | (n + 1) =>
      (sw_vertU x y0 n).append
        ((Walk.cons (sw_adj_vertSucc x (y0 + (n : ℤ))) Walk.nil).copy rfl
          (by norm_num [add_assoc]))



theorem sw_horizR_support_eq (y x0 : ℤ) (m : ℕ) :
    (sw_horizR y x0 (m + 1)).support
      = (sw_horizR y x0 m).support ++ [![x0 + (m : ℤ) + 1, y]] := by
  show ((sw_horizR y x0 m).append _).support = _
  rw [Walk.support_append, Walk.support_copy, Walk.support_cons, Walk.support_nil]
  rfl


theorem sw_vertU_support_eq (x y0 : ℤ) (m : ℕ) :
    (sw_vertU x y0 (m + 1)).support
      = (sw_vertU x y0 m).support ++ [![x, y0 + (m : ℤ) + 1]] := by
  show ((sw_vertU x y0 m).append _).support = _
  rw [Walk.support_append, Walk.support_copy, Walk.support_cons, Walk.support_nil]
  rfl



theorem sw_horizR_mem_support (y x0 : ℤ) (n : ℕ) (z : Site 2) :
    z ∈ (sw_horizR y x0 n).support
      ↔ ∃ t : ℤ, 0 ≤ t ∧ t ≤ (n : ℤ) ∧ z = ![x0 + t, y] := by
  induction n with
  | zero =>
    simp only [sw_horizR, Walk.support_copy, Walk.support_nil, List.mem_singleton]
    constructor
    · intro h; exact ⟨0, le_refl _, by norm_num, by rw [h]; norm_num⟩
    · rintro ⟨t, ht0, htn, rfl⟩
      have : t = 0 := le_antisymm (by exact_mod_cast htn) ht0
      simp [this]
  | succ m ih =>
    rw [sw_horizR_support_eq, List.mem_append, List.mem_singleton, ih]
    push_cast
    constructor
    · rintro (⟨t, ht0, htm, rfl⟩ | rfl)
      · exact ⟨t, ht0, by linarith, rfl⟩
      · exact ⟨(m : ℤ) + 1, by positivity, le_refl _, by norm_num [add_assoc]⟩
    · rintro ⟨t, ht0, htm, rfl⟩
      rcases eq_or_lt_of_le htm with h | h
      · right; rw [h]; ring_nf
      · left; exact ⟨t, ht0, by linarith, rfl⟩



theorem sw_vertU_mem_support (x y0 : ℤ) (n : ℕ) (z : Site 2) :
    z ∈ (sw_vertU x y0 n).support
      ↔ ∃ t : ℤ, 0 ≤ t ∧ t ≤ (n : ℤ) ∧ z = ![x, y0 + t] := by
  induction n with
  | zero =>
    simp only [sw_vertU, Walk.support_copy, Walk.support_nil, List.mem_singleton]
    constructor
    · intro h; exact ⟨0, le_refl _, by norm_num, by rw [h]; norm_num⟩
    · rintro ⟨t, ht0, htn, rfl⟩
      have : t = 0 := le_antisymm (by exact_mod_cast htn) ht0
      simp [this]
  | succ m ih =>
    rw [sw_vertU_support_eq, List.mem_append, List.mem_singleton, ih]
    push_cast
    constructor
    · rintro (⟨t, ht0, htm, rfl⟩ | rfl)
      · exact ⟨t, ht0, by linarith, rfl⟩
      · exact ⟨(m : ℤ) + 1, by positivity, le_refl _, by norm_num [add_assoc]⟩
    · rintro ⟨t, ht0, htm, rfl⟩
      rcases eq_or_lt_of_le htm with h | h
      · right; rw [h]; ring_nf
      · left; exact ⟨t, ht0, by linarith, rfl⟩


theorem sw_horizR_support_nodup (y x0 : ℤ) (n : ℕ) :
    (sw_horizR y x0 n).support.Nodup := by
  induction n with
  | zero => simp [sw_horizR]
  | succ m ih =>
    rw [sw_horizR_support_eq, List.nodup_append]
    refine ⟨ih, List.nodup_singleton _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    rw [sw_horizR_mem_support] at ha
    obtain ⟨t, ht0, htm, heq⟩ := ha
    intro hcontra
    rw [heq] at hcontra
    have hx : x0 + t = x0 + (m : ℤ) + 1 := by
      have := congrFun hcontra 0; simpa using this
    linarith


theorem sw_vertU_support_nodup (x y0 : ℤ) (n : ℕ) :
    (sw_vertU x y0 n).support.Nodup := by
  induction n with
  | zero => simp [sw_vertU]
  | succ m ih =>
    rw [sw_vertU_support_eq, List.nodup_append]
    refine ⟨ih, List.nodup_singleton _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    rw [sw_vertU_mem_support] at ha
    obtain ⟨t, ht0, htm, heq⟩ := ha
    intro hcontra
    rw [heq] at hcontra
    have hy : y0 + t = y0 + (m : ℤ) + 1 := by
      have := congrFun hcontra 1; simpa using this
    linarith





noncomputable def sw_horizSeg (y x0 x1 : ℤ) :
    (hypercubicLattice 2).Walk ![x0, y] ![x1, y] :=
  if h : x0 ≤ x1 then
    (sw_horizR y x0 (x1 - x0).toNat).copy rfl
      (by rw [Int.toNat_of_nonneg (by linarith)]; norm_num)
  else
    ((sw_horizR y x1 (x0 - x1).toNat).reverse).copy
      (by rw [Int.toNat_of_nonneg (by linarith)]; norm_num) rfl



noncomputable def sw_vertSeg (x y0 y1 : ℤ) :
    (hypercubicLattice 2).Walk ![x, y0] ![x, y1] :=
  if h : y0 ≤ y1 then
    (sw_vertU x y0 (y1 - y0).toNat).copy rfl
      (by rw [Int.toNat_of_nonneg (by linarith)]; norm_num)
  else
    ((sw_vertU x y1 (y0 - y1).toNat).reverse).copy
      (by rw [Int.toNat_of_nonneg (by linarith)]; norm_num) rfl



theorem sw_horizSeg_mem_support (y x0 x1 : ℤ) (z : Site 2) :
    z ∈ (sw_horizSeg y x0 x1).support
      ↔ ∃ t : ℤ, t ∈ Set.uIcc x0 x1 ∧ z = ![t, y] := by
  unfold sw_horizSeg
  by_cases h : x0 ≤ x1
  · rw [dif_pos h, Walk.support_copy, sw_horizR_mem_support, Set.uIcc_of_le h]
    constructor
    · rintro ⟨t, ht0, htn, rfl⟩
      rw [Int.toNat_of_nonneg (by linarith)] at htn
      exact ⟨x0 + t, ⟨by linarith, by linarith⟩, rfl⟩
    · rintro ⟨s, ⟨hs0, hs1⟩, rfl⟩
      refine ⟨s - x0, by linarith, ?_, by ring_nf⟩
      rw [Int.toNat_of_nonneg (by linarith)]; linarith
  · have hle : x1 ≤ x0 := le_of_lt (lt_of_not_ge h)
    rw [dif_neg h, Walk.support_copy, Walk.support_reverse, List.mem_reverse,
      sw_horizR_mem_support, Set.uIcc_of_ge hle]
    constructor
    · rintro ⟨t, ht0, htn, rfl⟩
      rw [Int.toNat_of_nonneg (by linarith)] at htn
      exact ⟨x1 + t, ⟨by linarith, by linarith⟩, rfl⟩
    · rintro ⟨s, ⟨hs1, hs0⟩, rfl⟩
      refine ⟨s - x1, by linarith, ?_, by ring_nf⟩
      rw [Int.toNat_of_nonneg (by linarith)]; linarith



theorem sw_vertSeg_mem_support (x y0 y1 : ℤ) (z : Site 2) :
    z ∈ (sw_vertSeg x y0 y1).support
      ↔ ∃ t : ℤ, t ∈ Set.uIcc y0 y1 ∧ z = ![x, t] := by
  unfold sw_vertSeg
  by_cases h : y0 ≤ y1
  · rw [dif_pos h, Walk.support_copy, sw_vertU_mem_support, Set.uIcc_of_le h]
    constructor
    · rintro ⟨t, ht0, htn, rfl⟩
      rw [Int.toNat_of_nonneg (by linarith)] at htn
      exact ⟨y0 + t, ⟨by linarith, by linarith⟩, rfl⟩
    · rintro ⟨s, ⟨hs0, hs1⟩, rfl⟩
      refine ⟨s - y0, by linarith, ?_, by ring_nf⟩
      rw [Int.toNat_of_nonneg (by linarith)]; linarith
  · have hle : y1 ≤ y0 := le_of_lt (lt_of_not_ge h)
    rw [dif_neg h, Walk.support_copy, Walk.support_reverse, List.mem_reverse,
      sw_vertU_mem_support, Set.uIcc_of_ge hle]
    constructor
    · rintro ⟨t, ht0, htn, rfl⟩
      rw [Int.toNat_of_nonneg (by linarith)] at htn
      exact ⟨y1 + t, ⟨by linarith, by linarith⟩, rfl⟩
    · rintro ⟨s, ⟨hs1, hs0⟩, rfl⟩
      refine ⟨s - y1, by linarith, ?_, by ring_nf⟩
      rw [Int.toNat_of_nonneg (by linarith)]; linarith




theorem sw_seg_support_mem (y x0 x1 a b : ℤ) :
    (![a, b] : Site 2) ∈ (sw_horizSeg y x0 x1).support
      ↔ b = y ∧ a ∈ Set.uIcc x0 x1 := by
  rw [sw_horizSeg_mem_support]
  constructor
  · rintro ⟨t, ht, heq⟩
    have ha : a = t := by have := congrFun heq 0; simpa using this
    have hb : b = y := by have := congrFun heq 1; simpa using this
    exact ⟨hb, ha ▸ ht⟩
  · rintro ⟨rfl, ha⟩
    exact ⟨a, ha, rfl⟩



theorem sw_horizSeg_support_subset (y x0 x1 : ℤ) :
    {z : Site 2 | z ∈ (sw_horizSeg y x0 x1).support}
      ⊆ (fun t => (![t, y] : Site 2)) '' Set.uIcc x0 x1 := by
  intro z hz
  rw [Set.mem_setOf_eq, sw_horizSeg_mem_support] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  exact ⟨t, ht, rfl⟩



theorem sw_vertSeg_support_subset (x y0 y1 : ℤ) :
    {z : Site 2 | z ∈ (sw_vertSeg x y0 y1).support}
      ⊆ (fun t => (![x, t] : Site 2)) '' Set.uIcc y0 y1 := by
  intro z hz
  rw [Set.mem_setOf_eq, sw_vertSeg_mem_support] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  exact ⟨t, ht, rfl⟩



theorem sw_horizSeg_support_nodup (y x0 x1 : ℤ) :
    (sw_horizSeg y x0 x1).support.Nodup := by
  unfold sw_horizSeg
  by_cases h : x0 ≤ x1
  · rw [dif_pos h, Walk.support_copy]; exact sw_horizR_support_nodup _ _ _
  · rw [dif_neg h, Walk.support_copy, Walk.support_reverse, List.nodup_reverse]
    exact sw_horizR_support_nodup _ _ _


theorem sw_vertSeg_support_nodup (x y0 y1 : ℤ) :
    (sw_vertSeg x y0 y1).support.Nodup := by
  unfold sw_vertSeg
  by_cases h : y0 ≤ y1
  · rw [dif_pos h, Walk.support_copy]; exact sw_vertU_support_nodup _ _ _
  · rw [dif_neg h, Walk.support_copy, Walk.support_reverse, List.nodup_reverse]
    exact sw_vertU_support_nodup _ _ _




theorem sw_seg_nodup_of_distinct (y x0 x1 : ℤ) (hne : x0 ≠ x1) :
    (sw_horizSeg y x0 x1).support.Nodup ∧ (![x0, y] : Site 2) ≠ ![x1, y] := by
  refine ⟨sw_horizSeg_support_nodup y x0 x1, ?_⟩
  intro hcontra
  exact hne (by have := congrFun hcontra 0; simpa using this)






noncomputable def sw_lshape (x0 y0 x1 y1 : ℤ) :
    (hypercubicLattice 2).Walk ![x0, y0] ![x1, y1] :=
  (sw_horizSeg y0 x0 x1).append (sw_vertSeg x1 y0 y1)



theorem sw_lshape_mem_support (x0 y0 x1 y1 : ℤ) (z : Site 2) :
    z ∈ (sw_lshape x0 y0 x1 y1).support
      ↔ z ∈ (sw_horizSeg y0 x0 x1).support ∨ z ∈ (sw_vertSeg x1 y0 y1).support := by
  unfold sw_lshape
  exact Walk.mem_support_append_iff _ _




theorem sw_lshape_support_eq (x0 y0 x1 y1 : ℤ) (z : Site 2) :
    z ∈ (sw_lshape x0 y0 x1 y1).support
      ↔ (∃ t : ℤ, t ∈ Set.uIcc x0 x1 ∧ z = ![t, y0])
        ∨ (∃ t : ℤ, t ∈ Set.uIcc y0 y1 ∧ z = ![x1, t]) := by
  rw [sw_lshape_mem_support, sw_horizSeg_mem_support, sw_vertSeg_mem_support]

end Lattice

end StatMech
