/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Sort
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Basic

/-! # Column-count bounds for median-of-medians selection -/

@[expose] public section

set_option autoImplicit false
universe u v
namespace Cslib.Algorithms.Lean.TimeM

private theorem medianOfMedians_countP_le_split {α : Type u} [LinearOrder α] (v : α) (l : List α) :
    l.countP (fun y => decide (y ≤ v))
      = l.countP (fun y => decide (y < v)) + l.countP (fun y => decide (y = v)) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rcases lt_trichotomy a v with h | h | h
    · rw [@List.countP_cons_of_pos α (fun y => decide (y ≤ v)) a t (decide_eq_true (le_of_lt h)),
          @List.countP_cons_of_pos α (fun y => decide (y < v)) a t (decide_eq_true h),
          @List.countP_cons_of_neg α (fun y => decide (y = v)) a t
            (by show ¬ decide (a = v) = true; rw [decide_eq_true_eq]; exact ne_of_lt h)]
      omega
    · rw [@List.countP_cons_of_pos α (fun y => decide (y ≤ v)) a t (decide_eq_true (le_of_eq h)),
          @List.countP_cons_of_neg α (fun y => decide (y < v)) a t
            (by show ¬ decide (a < v) = true; rw [decide_eq_true_eq, h]; exact lt_irrefl v),
          @List.countP_cons_of_pos α (fun y => decide (y = v)) a t (decide_eq_true h)]
      omega
    · rw [@List.countP_cons_of_neg α (fun y => decide (y ≤ v)) a t
            (by show ¬ decide (a ≤ v) = true; rw [decide_eq_true_eq]; exact not_le.2 h),
          @List.countP_cons_of_neg α (fun y => decide (y < v)) a t
            (by show ¬ decide (a < v) = true; rw [decide_eq_true_eq]; exact asymm h),
          @List.countP_cons_of_neg α (fun y => decide (y = v)) a t
            (by show ¬ decide (a = v) = true; rw [decide_eq_true_eq]; exact (ne_of_lt h).symm)]
      omega

private theorem medianOfMedians_countP_ge_split {α : Type u} [LinearOrder α] (v : α) (l : List α) :
    l.countP (fun y => decide (v ≤ y))
      = l.countP (fun y => decide (v < y)) + l.countP (fun y => decide (y = v)) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rcases lt_trichotomy v a with h | h | h
    · rw [@List.countP_cons_of_pos α (fun y => decide (v ≤ y)) a t (decide_eq_true (le_of_lt h)),
          @List.countP_cons_of_pos α (fun y => decide (v < y)) a t (decide_eq_true h),
          @List.countP_cons_of_neg α (fun y => decide (y = v)) a t
            (by show ¬ decide (a = v) = true; rw [decide_eq_true_eq]; exact (ne_of_lt h).symm)]
      omega
    · rw [@List.countP_cons_of_pos α (fun y => decide (v ≤ y)) a t (decide_eq_true (le_of_eq h)),
          @List.countP_cons_of_neg α (fun y => decide (v < y)) a t
            (by show ¬ decide (v < a) = true; rw [decide_eq_true_eq, h]; exact lt_irrefl a),
          @List.countP_cons_of_pos α (fun y => decide (y = v)) a t (decide_eq_true h.symm)]
      omega
    · rw [@List.countP_cons_of_neg α (fun y => decide (v ≤ y)) a t
            (by show ¬ decide (v ≤ a) = true; rw [decide_eq_true_eq]; exact not_le.2 h),
          @List.countP_cons_of_neg α (fun y => decide (v < y)) a t
            (by show ¬ decide (v < a) = true; rw [decide_eq_true_eq]; exact asymm h),
          @List.countP_cons_of_neg α (fun y => decide (y = v)) a t
            (by show ¬ decide (a = v) = true; rw [decide_eq_true_eq]; exact ne_of_lt h)]
      omega

private theorem medianOfMedians_countP_ge_add_lt {α : Type u} [LinearOrder α] (v : α) (l : List α) :
    l.countP (fun y => decide (v ≤ y)) + l.countP (fun y => decide (y < v)) = l.length := by
  rw [(List.length_eq_countP_add_countP (fun y => decide (v ≤ y)) (l := l))]
  congr 1
  apply List.countP_congr
  intro y _
  simp only [decide_eq_true_eq, not_le]

private theorem medianOfMedians_countP_eq_le_one {α : Type u} [LinearOrder α] (v : α) {l : List α} (h : l.Nodup) :
    l.countP (fun y => decide (y = v)) ≤ 1 := by
  have hcount := (List.nodup_iff_count_le_one.mp h) v
  have heq : l.countP (fun y => decide (y = v)) = l.count v := by
    apply List.countP_congr
    intro y _
    simp
  exact heq.le.trans hcount

private theorem medianOfMedians_countP_dropLast_ge {α : Type u} (r : α → Bool) : ∀ (l : List α),
    l.countP r ≤ l.dropLast.countP r + 1
  | [] => by simp
  | [a] => by cases h : r a <;> simp [List.dropLast_singleton, h]
  | a :: b :: t => by
      have ih := medianOfMedians_countP_dropLast_ge r (b :: t)
      rw [List.dropLast_cons_cons]
      simp only [List.countP_cons] at ih ⊢
      omega

/-! ### Forall₂ helpers -/

private theorem medianOfMedians_forall₂_dropLast {α : Type u} {β : Type v} {R : α → β → Prop}
    {l₁ : List α} {l₂ : List β} (h : List.Forall₂ R l₁ l₂) :
    List.Forall₂ R l₁.dropLast l₂.dropLast := by
  induction h with
  | nil => exact List.Forall₂.nil
  | @cons a b l₁ l₂ hab hr ih =>
    cases hr with
    | nil => exact List.Forall₂.nil
    | @cons a' b' l₁' l₂' ha'b' hr' =>
      rw [List.dropLast_cons_cons, List.dropLast_cons_cons]
      exact List.Forall₂.cons hab ih

private theorem medianOfMedians_forall₂_and_left {α : Type u} {β : Type v} {R : α → β → Prop} {S : α → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → (∀ a ∈ l₁, S a) →
      List.Forall₂ (fun a b => S a ∧ R a b) l₁ l₂ := by
  intro l₁ l₂ h hs
  exact (List.forall₂_and_left l₁ l₂).mpr ⟨hs, h⟩

private theorem medianOfMedians_sum_bound {α : Type u} (q r : α → Bool) {gs : List (List α)} {ms : List α}
    (h : List.Forall₂ (fun g x => (if r x = true then 3 else 0) ≤ g.countP q) gs ms) :
    3 * ms.countP r ≤ gs.flatten.countP q := by
  induction h with
  | nil => simp
  | @cons g x gs' ms' hgx hrest ih =>
    rw [List.flatten_cons, List.countP_append, List.countP_cons]
    rcases hb : r x with _ | _ <;>
      simp only [hb, reduceIte, Bool.false_eq_true] at hgx ⊢ <;> omega

private theorem medianOfMedians_mem_flatten_of_forall₂ {α : Type u} {gs : List (List α)} {ms : List α}
    (h : List.Forall₂ (fun g x => x ∈ g) gs ms) : ∀ x ∈ ms, x ∈ gs.flatten := by
  induction h with
  | nil => simp
  | @cons g x gs' ms' hgx hrest ih =>
    intro y hy
    rw [List.flatten_cons, List.mem_append]
    rcases List.mem_cons.1 hy with h1 | h2
    · subst h1; exact Or.inl hgx
    · exact Or.inr (ih y h2)

private theorem medianOfMedians_nodup_medians {α : Type u} {gs : List (List α)} {ms : List α}
    (h : List.Forall₂ (fun g x => x ∈ g) gs ms) : gs.flatten.Nodup → ms.Nodup := by
  induction h with
  | nil => intro _; exact List.nodup_nil
  | @cons g x gs' ms' hgx hrest ih =>
    intro hn
    rw [List.flatten_cons, List.nodup_append] at hn
    rw [List.nodup_cons]
    exact ⟨fun hx => hn.2.2 x hgx x (medianOfMedians_mem_flatten_of_forall₂ hrest x hx) rfl, ih hn.2.1⟩

/-! ### Per-group contribution lemmas (full groups contribute ≥ 3) -/

private theorem medianOfMedians_contrib_le {α : Type u} [LinearOrder α] (pivot : α) {g : List α} {x : α}
    (hlen : g.length = 5)
    (hle : (g.length - 1) / 2 < g.countP (fun y => decide (y ≤ x))) :
    (if decide (x ≤ pivot) = true then 3 else 0) ≤ g.countP (fun y => decide (y ≤ pivot)) := by
  split
  · rename_i hr
    have hxp : x ≤ pivot := of_decide_eq_true hr
    have h3 : (3:ℕ) ≤ g.countP (fun y => decide (y ≤ x)) := by rw [hlen] at hle; omega
    exact le_trans h3 (List.countP_mono_left (fun y _ hy =>
      decide_eq_true (le_trans (of_decide_eq_true hy) hxp)))
  · exact Nat.zero_le _

private theorem medianOfMedians_contrib_lt {α : Type u} [LinearOrder α] (pivot : α) {g : List α} {x : α}
    (hlen : g.length = 5)
    (hle : (g.length - 1) / 2 < g.countP (fun y => decide (y ≤ x))) :
    (if decide (x < pivot) = true then 3 else 0) ≤ g.countP (fun y => decide (y < pivot)) := by
  split
  · rename_i hr
    have hxp : x < pivot := of_decide_eq_true hr
    have h3 : (3:ℕ) ≤ g.countP (fun y => decide (y ≤ x)) := by rw [hlen] at hle; omega
    exact le_trans h3 (List.countP_mono_left (fun y _ hy =>
      decide_eq_true (lt_of_le_of_lt (of_decide_eq_true hy) hxp)))
  · exact Nat.zero_le _

private theorem medianOfMedians_contrib_ge {α : Type u} [LinearOrder α] (pivot : α) {g : List α} {x : α}
    (hlen : g.length = 5)
    (hlt : g.countP (fun y => decide (y < x)) ≤ (g.length - 1) / 2) :
    (if decide (pivot ≤ x) = true then 3 else 0) ≤ g.countP (fun y => decide (pivot ≤ y)) := by
  split
  · rename_i hr
    have hxp : pivot ≤ x := of_decide_eq_true hr
    have hcompl := medianOfMedians_countP_ge_add_lt x g
    have h3 : (3:ℕ) ≤ g.countP (fun y => decide (x ≤ y)) := by rw [hlen] at hlt hcompl; omega
    exact le_trans h3 (List.countP_mono_left (fun y _ hy =>
      decide_eq_true (le_trans hxp (of_decide_eq_true hy))))
  · exact Nat.zero_le _

private theorem medianOfMedians_contrib_gt {α : Type u} [LinearOrder α] (pivot : α) {g : List α} {x : α}
    (hlen : g.length = 5)
    (hlt : g.countP (fun y => decide (y < x)) ≤ (g.length - 1) / 2) :
    (if decide (pivot < x) = true then 3 else 0) ≤ g.countP (fun y => decide (pivot < y)) := by
  split
  · rename_i hr
    have hxp : pivot < x := of_decide_eq_true hr
    have hcompl := medianOfMedians_countP_ge_add_lt x g
    have h3 : (3:ℕ) ≤ g.countP (fun y => decide (x ≤ y)) := by rw [hlen] at hlt hcompl; omega
    exact le_trans h3 (List.countP_mono_left (fun y _ hy =>
      decide_eq_true (lt_of_lt_of_le hxp (of_decide_eq_true hy))))
  · exact Nat.zero_le _

/-! ### Main discard bounds -/

theorem medianOfMedians_weak_discard_bound {α : Type u} [LinearOrder α]
    (groups : List (List α)) (medians : List α) (pivot : α) :
    groups.length = (groups.flatten.length + 4) / 5 →
    (∀ group ∈ groups.dropLast, group.length = 5) →
    List.Forall₂ (fun group x => x ∈ group ∧
      group.countP (fun y => decide (y < x)) ≤ (group.length - 1) / 2 ∧
      (group.length - 1) / 2 < group.countP (fun y => decide (y ≤ x))) groups medians →
    (medians.countP (fun y => decide (y < pivot)) ≤ medians.length / 2 ∧
      medians.length / 2 < medians.countP (fun y => decide (y ≤ pivot))) →
    3 * ((groups.flatten.length + 9) / 10 - 2) ≤
        groups.flatten.countP (fun y => decide (y ≤ pivot)) ∧
      3 * ((groups.flatten.length + 9) / 10 - 2) ≤
        groups.flatten.countP (fun y => decide (pivot ≤ y)) := by
  intro h1 h3 h4 h5
  obtain ⟨hlt_med, hle_med⟩ := h5
  have hmlen : medians.length = (groups.flatten.length + 4) / 5 := by
    rw [← h4.length_eq]; exact h1
  have hd := medianOfMedians_forall₂_dropLast h4
  have hcomb := medianOfMedians_forall₂_and_left hd h3
  -- lower (y ≤ pivot)
  have hsumL := medianOfMedians_sum_bound (fun y => decide (y ≤ pivot)) (fun x => decide (x ≤ pivot))
    (hcomb.imp (fun g x hgx => medianOfMedians_contrib_le pivot hgx.1 hgx.2.2.2))
  have hsubL : groups.dropLast.flatten.countP (fun y => decide (y ≤ pivot))
      ≤ groups.flatten.countP (fun y => decide (y ≤ pivot)) :=
    List.Sublist.countP_le ((List.dropLast_sublist groups).flatten)
  have hdropL := medianOfMedians_countP_dropLast_ge (fun x => decide (x ≤ pivot)) medians
  -- upper (pivot ≤ y)
  have hsumU := medianOfMedians_sum_bound (fun y => decide (pivot ≤ y)) (fun x => decide (pivot ≤ x))
    (hcomb.imp (fun g x hgx => medianOfMedians_contrib_ge pivot hgx.1 hgx.2.2.1))
  have hsubU : groups.dropLast.flatten.countP (fun y => decide (pivot ≤ y))
      ≤ groups.flatten.countP (fun y => decide (pivot ≤ y)) :=
    List.Sublist.countP_le ((List.dropLast_sublist groups).flatten)
  have hdropU := medianOfMedians_countP_dropLast_ge (fun x => decide (pivot ≤ x)) medians
  have hcomplU := medianOfMedians_countP_ge_add_lt pivot medians
  refine ⟨?_, ?_⟩
  · omega
  · omega

theorem medianOfMedians_strict_discard_bound {α : Type u} [LinearOrder α]
    (groups : List (List α)) (medians : List α) (pivot : α) :
    groups.length = (groups.flatten.length + 4) / 5 →
    (∀ group ∈ groups.dropLast, group.length = 5) →
    List.Forall₂ (fun group x => x ∈ group ∧
      group.countP (fun y => decide (y < x)) ≤ (group.length - 1) / 2 ∧
      (group.length - 1) / 2 < group.countP (fun y => decide (y ≤ x))) groups medians →
    (medians.countP (fun y => decide (y < pivot)) ≤ medians.length / 2 ∧
      medians.length / 2 < medians.countP (fun y => decide (y ≤ pivot))) →
    groups.flatten.Nodup →
    3 * ((groups.flatten.length + 9) / 10 - 2) ≤
        groups.flatten.countP (fun y => decide (y < pivot)) ∧
      3 * ((groups.flatten.length + 9) / 10 - 2) ≤
        groups.flatten.countP (fun y => decide (pivot < y)) := by
  intro h1 h3 h4 h5 h6
  obtain ⟨hlt_med, hle_med⟩ := h5
  have hmlen : medians.length = (groups.flatten.length + 4) / 5 := by
    rw [← h4.length_eq]; exact h1
  have hnd : medians.Nodup := medianOfMedians_nodup_medians (h4.imp (fun g x hgx => hgx.1)) h6
  have hb := medianOfMedians_countP_eq_le_one pivot hnd
  have hd := medianOfMedians_forall₂_dropLast h4
  have hcomb := medianOfMedians_forall₂_and_left hd h3
  -- lower (y < pivot)
  have hsumL := medianOfMedians_sum_bound (fun y => decide (y < pivot)) (fun x => decide (x < pivot))
    (hcomb.imp (fun g x hgx => medianOfMedians_contrib_lt pivot hgx.1 hgx.2.2.2))
  have hsubL : groups.dropLast.flatten.countP (fun y => decide (y < pivot))
      ≤ groups.flatten.countP (fun y => decide (y < pivot)) :=
    List.Sublist.countP_le ((List.dropLast_sublist groups).flatten)
  have hdropL := medianOfMedians_countP_dropLast_ge (fun x => decide (x < pivot)) medians
  have hsplitL := medianOfMedians_countP_le_split pivot medians
  -- upper (pivot < y)
  have hsumU := medianOfMedians_sum_bound (fun y => decide (pivot < y)) (fun x => decide (pivot < x))
    (hcomb.imp (fun g x hgx => medianOfMedians_contrib_gt pivot hgx.1 hgx.2.2.1))
  have hsubU : groups.dropLast.flatten.countP (fun y => decide (pivot < y))
      ≤ groups.flatten.countP (fun y => decide (pivot < y)) :=
    List.Sublist.countP_le ((List.dropLast_sublist groups).flatten)
  have hdropU := medianOfMedians_countP_dropLast_ge (fun x => decide (pivot < x)) medians
  have hsplitU := medianOfMedians_countP_ge_split pivot medians
  have hcomplU := medianOfMedians_countP_ge_add_lt pivot medians
  refine ⟨?_, ?_⟩
  · omega
  · omega

end Cslib.Algorithms.Lean.TimeM
