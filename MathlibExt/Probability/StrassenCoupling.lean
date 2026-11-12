/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Star
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

@[expose] public section

section
open Finset

namespace MathlibExt.Probability.StrassenCouplingWanted

/-!
# Finite Strassen stochastic domination
-/

/-- **Finite upper sets.** A finite subset $U$ of a preordered set $\alpha$ is an upper set (is
upward closed) if for all $x, y \in \alpha$ with $x \in U$ and $x \le y$, also $y \in U$. -/
def IsUpperSet {α : Type*} [Preorder α] (U : Finset α) : Prop :=
  ∀ ⦃x y : α⦄, x ∈ U → x ≤ y → y ∈ U

/-- upper set of the sub-poset carried by `s`. -/
private def UpOn {α : Type*} [Preorder α] (s U : Finset α) : Prop :=
  U ⊆ s ∧ ∀ ⦃x⦄, x ∈ U → ∀ ⦃y⦄, y ∈ s → x ≤ y → y ∈ U

/-- support-count of `p` inside `s`. -/
private noncomputable def sp {α : Type*} (s : Finset α) (p : α → ℝ) : ℕ :=
  (s.filter (fun x => p x ≠ 0)).card

/-- combined measure. -/
private noncomputable def M {α : Type*} (s : Finset α) (p q : α → ℝ) : ℕ :=
  s.card * (2 * s.card + 1) + (sp s p + sp s q)

private lemma sp_le {α : Type*} (s : Finset α) (p : α → ℝ) : sp s p ≤ s.card :=
  (Finset.card_filter_le _ _)

private lemma M_lt {α : Type*} (c d : Finset α) (hcd : c.card < d.card)
    (a b p q : α → ℝ) : M c a b < M d p q := by
  have h1 : sp c a ≤ c.card := sp_le c a
  have h2 : sp c b ≤ c.card := sp_le c b
  simp only [M]
  nlinarith [hcd, h1, h2, Nat.zero_le (sp d p), Nat.zero_le (sp d q)]

/-- The hypotheses of the carrier-form coupling problem. -/
private def Hyps {α : Type*} [PartialOrder α] (s : Finset α) (p q : α → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ (∀ x, 0 ≤ q x) ∧
  (∀ x, x ∉ s → p x = 0) ∧ (∀ x, x ∉ s → q x = 0) ∧
  (∑ x ∈ s, p x = ∑ x ∈ s, q x) ∧
  (∀ U, UpOn s U → ∑ x ∈ U, p x ≤ ∑ x ∈ U, q x)

/-- The conclusion: a coupling supported on `{x ≤ y}` and inside `s × s`. -/
private def Concl {α : Type*} [Preorder α] (s : Finset α) (p q : α → ℝ) : Prop :=
  ∃ π : α → α → ℝ, (∀ x y, 0 ≤ π x y) ∧
    (∀ x, ∑ y ∈ s, π x y = p x) ∧ (∀ y, ∑ x ∈ s, π x y = q y) ∧
    (∀ x y, ¬ x ≤ y → π x y = 0) ∧ (∀ x y, π x y ≠ 0 → x ∈ s ∧ y ∈ s)

/-- Trivial case: `p ≡ 0` on `s` forces `q ≡ 0` and the zero coupling works. -/
private lemma coupling_trivial {α : Type*} [PartialOrder α] (s : Finset α) (p q : α → ℝ)
    (hq : ∀ x, 0 ≤ q x) (hps : ∀ x, x ∉ s → p x = 0) (hqs : ∀ x, x ∉ s → q x = 0)
    (hsum : ∑ x ∈ s, p x = ∑ x ∈ s, q x) (hp0 : ∀ x ∈ s, p x = 0) : Concl s p q := by
  have hpall : ∀ x, p x = 0 := by
    intro x; by_cases hx : x ∈ s
    · exact hp0 x hx
    · exact hps x hx
  have hsum0 : ∑ x ∈ s, q x = 0 := by
    rw [← hsum]; exact Finset.sum_eq_zero (fun x hx => hp0 x hx)
  have hqall : ∀ x, q x = 0 := by
    intro x; by_cases hx : x ∈ s
    · exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hq i)).1 hsum0 x hx
    · exact hqs x hx
  refine ⟨fun _ _ => 0, fun _ _ => le_refl 0, ?_, ?_, ?_, ?_⟩
  · intro x; simp [hpall x]
  · intro y; simp [hqall y]
  · intro x y _; rfl
  · intro x y h; exact absurd rfl h

/-- `UpOn` transports along carriers: an upper set of the sub-poset `U` is upper in `s`. -/
private lemma upOn_of_sub {α : Type*} [Preorder α] {s U V : Finset α}
    (hU : UpOn s U) (hV : UpOn U V) : UpOn s V :=
  ⟨hV.1.trans hU.1, fun _x hxV _y hys hxy => hV.2 hxV (hU.2 (hV.1 hxV) hys hxy) hxy⟩

/-- Split at a tight nontrivial upper set `U`. -/
private lemma coupling_split {α : Type*} [PartialOrder α]
    (s U : Finset α) (p q : α → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hps : ∀ x, x ∉ s → p x = 0) (hqs : ∀ x, x ∉ s → q x = 0)
    (hsum : ∑ x ∈ s, p x = ∑ x ∈ s, q x)
    (hUp : ∀ U', UpOn s U' → ∑ x ∈ U', p x ≤ ∑ x ∈ U', q x)
    (hUup : UpOn s U) (hUtight : ∑ x ∈ U, p x = ∑ x ∈ U, q x)
    (hUne : U.Nonempty) (hUlt : U ⊂ s)
    (ih : ∀ (s' : Finset α) (p' q' : α → ℝ),
        M s' p' q' < M s p q → Hyps s' p' q' → Concl s' p' q') :
    Concl s p q := by
  classical
  have hUsub : U ⊆ s := hUup.1
  set p₁ : α → ℝ := fun x => if x ∈ U then p x else 0 with hp₁def
  set q₁ : α → ℝ := fun x => if x ∈ U then q x else 0 with hq₁def
  set p₂ : α → ℝ := fun x => if x ∈ s \ U then p x else 0 with hp₂def
  set q₂ : α → ℝ := fun x => if x ∈ s \ U then q x else 0 with hq₂def
  have rp1 : ∀ V : Finset α, V ⊆ U → ∑ x ∈ V, p₁ x = ∑ x ∈ V, p x :=
    fun V hV => Finset.sum_congr rfl (fun x hx => by simp only [hp₁def]; exact ite_eq_left (hV hx))
  have rq1 : ∀ V : Finset α, V ⊆ U → ∑ x ∈ V, q₁ x = ∑ x ∈ V, q x :=
    fun V hV => Finset.sum_congr rfl (fun x hx => by simp only [hq₁def]; exact ite_eq_left (hV hx))
  have rp2 : ∀ V : Finset α, V ⊆ s \ U → ∑ x ∈ V, p₂ x = ∑ x ∈ V, p x :=
    fun V hV => Finset.sum_congr rfl (fun x hx => by simp only [hp₂def]; exact ite_eq_left (hV hx))
  have rq2 : ∀ V : Finset α, V ⊆ s \ U → ∑ x ∈ V, q₂ x = ∑ x ∈ V, q x :=
    fun V hV => Finset.sum_congr rfl (fun x hx => by simp only [hq₂def]; exact ite_eq_left (hV hx))
  -- Subproblem 1 on U
  have hCU : Concl U p₁ q₁ := by
    apply ih U p₁ q₁ (M_lt U s (Finset.card_lt_card hUlt) _ _ p q)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x; simp only [hp₁def]; split_ifs; exacts [hp x, le_refl 0]
    · intro x; simp only [hq₁def]; split_ifs; exacts [hq x, le_refl 0]
    · intro x hx; simp only [hp₁def]; exact ite_eq_right hx
    · intro x hx; simp only [hq₁def]; exact ite_eq_right hx
    · rw [rp1 U (subset_refl U), rq1 U (subset_refl U)]; exact hUtight
    · intro V hV
      rw [rp1 V hV.1, rq1 V hV.1]
      exact hUp V (upOn_of_sub hUup hV)
  -- Subproblem 2 on s \ U
  have hCU2 : Concl (s \ U) p₂ q₂ := by
    apply ih (s \ U) p₂ q₂
      (M_lt (s \ U) s (Finset.card_lt_card (Finset.sdiff_ssubset hUsub hUne)) _ _ p q)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x; simp only [hp₂def]; split_ifs; exacts [hp x, le_refl 0]
    · intro x; simp only [hq₂def]; split_ifs; exacts [hq x, le_refl 0]
    · intro x hx; simp only [hp₂def]; exact ite_eq_right hx
    · intro x hx; simp only [hq₂def]; exact ite_eq_right hx
    · rw [rp2 (s \ U) (subset_refl _), rq2 (s \ U) (subset_refl _)]
      have e1 : ∑ x ∈ s \ U, p x + ∑ x ∈ U, p x = ∑ x ∈ s, p x := Finset.sum_sdiff hUsub
      have e2 : ∑ x ∈ s \ U, q x + ∑ x ∈ U, q x = ∑ x ∈ s, q x := Finset.sum_sdiff hUsub
      linarith [hsum, hUtight]
    · intro V hV
      rw [rp2 V hV.1, rq2 V hV.1]
      have hdisj : Disjoint V U :=
        Finset.disjoint_left.2 (fun a haV haU => (Finset.mem_sdiff.1 (hV.1 haV)).2 haU)
      have hVUup : UpOn s (V ∪ U) := by
        refine ⟨Finset.union_subset (hV.1.trans Finset.sdiff_subset) hUsub, ?_⟩
        intro x hx y hys hxy
        rcases Finset.mem_union.1 hx with hxV | hxU
        · by_cases hyU : y ∈ U
          · exact Finset.mem_union.2 (Or.inr hyU)
          · exact Finset.mem_union.2 (Or.inl (hV.2 hxV (Finset.mem_sdiff.2 ⟨hys, hyU⟩) hxy))
        · exact Finset.mem_union.2 (Or.inr (hUup.2 hxU hys hxy))
      have hle := hUp (V ∪ U) hVUup
      rw [Finset.sum_union hdisj, Finset.sum_union hdisj] at hle
      linarith [hUtight]
  obtain ⟨π₁, h1pos, h1row, h1col, h1supp, h1in⟩ := hCU
  obtain ⟨π₂, h2pos, h2row, h2col, h2supp, h2in⟩ := hCU2
  refine ⟨fun x y => π₁ x y + π₂ x y, fun x y => add_nonneg (h1pos x y) (h2pos x y), ?_, ?_, ?_, ?_⟩
  · intro x
    rw [Finset.sum_add_distrib]
    have e1 : ∑ y ∈ s, π₁ x y = p₁ x := by
      rw [← h1row x]
      exact (Finset.sum_subset hUsub (fun y _ hyU => by
        by_contra h; exact hyU (h1in x y h).2)).symm
    have e2 : ∑ y ∈ s, π₂ x y = p₂ x := by
      rw [← h2row x]
      exact (Finset.sum_subset Finset.sdiff_subset (fun y _ hyU => by
        by_contra h; exact hyU (h2in x y h).2)).symm
    rw [e1, e2]
    by_cases hxU : x ∈ U
    · simp [hp₁def, hp₂def, hxU, Finset.mem_sdiff]
    · by_cases hxs : x ∈ s
      · simp [hp₁def, hp₂def, hxU, hxs, Finset.mem_sdiff]
      · simp [hp₁def, hp₂def, hxU, hxs, hps x hxs, Finset.mem_sdiff]
  · intro y
    rw [Finset.sum_add_distrib]
    have e1 : ∑ x ∈ s, π₁ x y = q₁ y := by
      rw [← h1col y]
      exact (Finset.sum_subset hUsub (fun x _ hxU => by
        by_contra h; exact hxU (h1in x y h).1)).symm
    have e2 : ∑ x ∈ s, π₂ x y = q₂ y := by
      rw [← h2col y]
      exact (Finset.sum_subset Finset.sdiff_subset (fun x _ hxU => by
        by_contra h; exact hxU (h2in x y h).1)).symm
    rw [e1, e2]
    by_cases hyU : y ∈ U
    · simp [hq₁def, hq₂def, hyU, Finset.mem_sdiff]
    · by_cases hys : y ∈ s
      · simp [hq₁def, hq₂def, hyU, hys, Finset.mem_sdiff]
      · simp [hq₁def, hq₂def, hyU, hys, hqs y hys, Finset.mem_sdiff]
  · intro x y hxy
    change π₁ x y + π₂ x y = 0
    rw [h1supp x y hxy, h2supp x y hxy, add_zero]
  · intro x y hne
    have hne' : π₁ x y + π₂ x y ≠ 0 := hne
    by_cases h1 : π₁ x y = 0
    · have h2 : π₂ x y ≠ 0 := by intro h2; exact hne' (by rw [h1, h2, add_zero])
      exact ⟨(Finset.mem_sdiff.1 (h2in x y h2).1).1, (Finset.mem_sdiff.1 (h2in x y h2).2).1⟩
    · exact ⟨hUsub (h1in x y h1).1, hUsub (h1in x y h1).2⟩

/-- Pushing `t` units of flow along `a ≤ b` preserves the hypotheses. -/
private lemma push_hyps {α : Type*} [PartialOrder α] [DecidableEq α]
    (s : Finset α) (p q : α → ℝ) (a b : α) (t : ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hps : ∀ x, x ∉ s → p x = 0) (hqs : ∀ x, x ∉ s → q x = 0)
    (hsum : ∑ x ∈ s, p x = ∑ x ∈ s, q x)
    (hUp : ∀ U', UpOn s U' → ∑ x ∈ U', p x ≤ ∑ x ∈ U', q x)
    (hab : a ≤ b) (ha : a ∈ s) (hb : b ∈ s)
    (_ht0 : 0 ≤ t) (hta : t ≤ p a) (htb : t ≤ q b)
    (hslack : ∀ U', UpOn s U' → a ∉ U' → b ∈ U' → t ≤ ∑ x ∈ U', q x - ∑ x ∈ U', p x) :
    Hyps s (fun x => p x - if x = a then t else 0) (fun y => q y - if y = b then t else 0) := by
  have hpp : ∀ (T : Finset α), ∑ x ∈ T, (p x - if x = a then t else 0)
      = (∑ x ∈ T, p x) - (if a ∈ T then t else 0) := by
    intro T; simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq']
  have hqq : ∀ (T : Finset α), ∑ x ∈ T, (q x - if x = b then t else 0)
      = (∑ x ∈ T, q x) - (if b ∈ T then t else 0) := by
    intro T; simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change 0 ≤ p x - (if x = a then t else 0)
    by_cases hx : x = a
    · subst hx; rw [ite_eq_left rfl]; linarith [hta]
    · rw [ite_eq_right hx, sub_zero]; exact hp x
  · intro y
    change 0 ≤ q y - (if y = b then t else 0)
    by_cases hy : y = b
    · subst hy; rw [ite_eq_left rfl]; linarith [htb]
    · rw [ite_eq_right hy, sub_zero]; exact hq y
  · intro x hx
    have hxa : x ≠ a := fun h => hx (h ▸ ha)
    change p x - (if x = a then t else 0) = 0
    rw [ite_eq_right hxa, sub_zero]; exact hps x hx
  · intro y hy
    have hyb : y ≠ b := fun h => hy (h ▸ hb)
    change q y - (if y = b then t else 0) = 0
    rw [ite_eq_right hyb, sub_zero]; exact hqs y hy
  · rw [hpp s, hqq s, ite_eq_left ha, ite_eq_left hb, hsum]
  · intro U' hU'
    rw [hpp U', hqq U']
    by_cases haU : a ∈ U'
    · have hbU : b ∈ U' := hU'.2 haU hb hab
      rw [ite_eq_left haU, ite_eq_left hbU]; linarith [hUp U' hU']
    · rw [ite_eq_right haU]
      by_cases hbU : b ∈ U'
      · rw [ite_eq_left hbU]; linarith [hslack U' hU' haU hbU]
      · rw [ite_eq_right hbU]; linarith [hUp U' hU']

/-- Reconstruct a coupling for `(p, q)` from one for the pushed `(p', q')`. -/
private lemma push_concl {α : Type*} [PartialOrder α] [DecidableEq α]
    (s : Finset α) (p q : α → ℝ) (a b : α) (t : ℝ)
    (_hps : ∀ x, x ∉ s → p x = 0) (_hqs : ∀ x, x ∉ s → q x = 0)
    (hab : a ≤ b) (ha : a ∈ s) (hb : b ∈ s) (ht0 : 0 ≤ t)
    (hC : Concl s (fun x => p x - if x = a then t else 0)
                  (fun y => q y - if y = b then t else 0)) :
    Concl s p q := by
  obtain ⟨π', hpos, hrow, hcol, hsupp, hin⟩ := hC
  refine ⟨fun x y => π' x y + (if x = a ∧ y = b then t else 0), ?_, ?_, ?_, ?_, ?_⟩
  · intro x y; by_cases h : x = a ∧ y = b
    · simp only [ite_eq_left h]; linarith [hpos x y]
    · simp only [ite_eq_right h, add_zero]; exact hpos x y
  · intro x
    rw [Finset.sum_add_distrib, hrow x]
    have hf : ∑ y ∈ s, (if x = a ∧ y = b then t else 0) = if x = a then t else 0 := by
      by_cases hxa : x = a
      · have hcongr : ∑ y ∈ s, (if x = a ∧ y = b then t else 0)
            = ∑ y ∈ s, (if y = b then t else 0) := Finset.sum_congr rfl (fun y _ => by simp [hxa])
        rw [hcongr, Finset.sum_ite_eq' s b (fun _ => t), ite_eq_left hb, ite_eq_left hxa]
      · have hz : ∑ y ∈ s, (if x = a ∧ y = b then t else 0) = 0 :=
          Finset.sum_eq_zero (fun y _ => ite_eq_right (fun h => hxa h.1))
        rw [hz, ite_eq_right hxa]
    rw [hf]; by_cases hxa : x = a <;> simp [hxa]
  · intro y
    rw [Finset.sum_add_distrib, hcol y]
    have hf : ∑ x ∈ s, (if x = a ∧ y = b then t else 0) = if y = b then t else 0 := by
      by_cases hyb : y = b
      · have hcongr : ∑ x ∈ s, (if x = a ∧ y = b then t else 0)
            = ∑ x ∈ s, (if x = a then t else 0) := Finset.sum_congr rfl (fun x _ => by simp [hyb])
        rw [hcongr, Finset.sum_ite_eq' s a (fun _ => t), ite_eq_left ha, ite_eq_left hyb]
      · have hz : ∑ x ∈ s, (if x = a ∧ y = b then t else 0) = 0 :=
          Finset.sum_eq_zero (fun x _ => ite_eq_right (fun h => hyb h.2))
        rw [hz, ite_eq_right hyb]
    rw [hf]; by_cases hyb : y = b <;> simp [hyb]
  · intro x y hxy
    have h : ¬ (x = a ∧ y = b) := fun ⟨hx, hy⟩ => hxy (hx ▸ hy ▸ hab)
    simp only [ite_eq_right h, add_zero]; exact hsupp x y hxy
  · intro x y hne
    by_cases h : x = a ∧ y = b
    · exact ⟨h.1 ▸ ha, h.2 ▸ hb⟩
    · have : π' x y ≠ 0 := by
        simp only [ite_eq_right h, add_zero] at hne; exact hne
      exact hin x y this

private lemma sp_mono {α : Type*} (s : Finset α) (f g : α → ℝ)
    (h : ∀ x ∈ s, g x ≠ 0 → f x ≠ 0) : sp s g ≤ sp s f := by
  simp only [sp]
  apply Finset.card_le_card
  intro x hx; rw [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, h x hx.1 hx.2⟩

private lemma sp_lt {α : Type*} (s : Finset α) (f g : α → ℝ) (a : α)
    (haS : a ∈ s) (hfa : f a ≠ 0) (hga : g a = 0)
    (h : ∀ x ∈ s, g x ≠ 0 → f x ≠ 0) : sp s g < sp s f := by
  simp only [sp]
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset ?_).mpr ⟨a, ?_, ?_⟩)
  · intro x hx; rw [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, h x hx.1 hx.2⟩
  · rw [Finset.mem_filter]; exact ⟨haS, hfa⟩
  · rw [Finset.mem_filter]; rintro ⟨_, hne⟩; exact hne hga

private lemma M_push_lt {α : Type*} (s : Finset α) (p q p' q' : α → ℝ)
    (h : sp s p' + sp s q' < sp s p + sp s q) : M s p' q' < M s p q := by
  simp only [M]
  set K := s.card * (2 * s.card + 1)
  omega

/-- Main carrier-form existence, by strong induction on the measure `M`. -/
private lemma exists_coupling_carrier {α : Type*} [PartialOrder α]
    (n : ℕ) : ∀ (s : Finset α) (p q : α → ℝ), M s p q ≤ n → Hyps s p q → Concl s p q := by
  classical
  induction n with
  | zero =>
    intro s p q hM hyps
    obtain ⟨hp, hq, hps, hqs, hsum, hUp⟩ := hyps
    have hcard : s.card = 0 := by simp only [M] at hM; nlinarith [Nat.zero_le (sp s p + sp s q)]
    have hse : s = ∅ := Finset.card_eq_zero.1 hcard
    exact coupling_trivial s p q hq hps hqs hsum
      (fun x hx => absurd (hse ▸ hx) (Finset.notMem_empty x))
  | succ n ih =>
    intro s p q hM hyps
    obtain ⟨hp, hq, hps, hqs, hsum, hUp⟩ := hyps
    classical
    have ih' : ∀ (s' : Finset α) (p' q' : α → ℝ),
        M s' p' q' < M s p q → Hyps s' p' q' → Concl s' p' q' :=
      fun s' p' q' hlt h => ih s' p' q' (by omega) h
    by_cases hp0 : ∀ x ∈ s, p x = 0
    · exact coupling_trivial s p q hq hps hqs hsum hp0
    push Not at hp0
    obtain ⟨a, haS, hpa⟩ := hp0
    have hpa' : 0 < p a := lt_of_le_of_ne (hp a) (Ne.symm hpa)
    -- Find `b ≥ a` in `s` with `q b > 0`.
    set Ua := s.filter (fun y => a ≤ y) with hUadef
    have haUa : a ∈ Ua := by rw [hUadef, Finset.mem_filter]; exact ⟨haS, le_refl a⟩
    have hUaup : UpOn s Ua := by
      refine ⟨Finset.filter_subset _ _, ?_⟩
      intro x hx y hys hxy
      rw [hUadef, Finset.mem_filter] at hx ⊢
      exact ⟨hys, le_trans hx.2 hxy⟩
    have hsumpos : 0 < ∑ y ∈ Ua, q y :=
      lt_of_lt_of_le (Finset.sum_pos' (fun i _ => hp i) ⟨a, haUa, hpa'⟩) (hUp Ua hUaup)
    obtain ⟨b, hbUa, hqb⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt hsumpos)
    have hbS : b ∈ s := Finset.filter_subset _ _ hbUa
    have hab : a ≤ b := by rw [hUadef, Finset.mem_filter] at hbUa; exact hbUa.2
    -- Tight-cut case split.
    by_cases hT : ∃ U, UpOn s U ∧ U.Nonempty ∧ U ⊂ s ∧ ∑ x ∈ U, p x = ∑ x ∈ U, q x
    · obtain ⟨U, hUup, hUne, hUlt, hUtight⟩ := hT
      exact coupling_split s U p q hp hq hps hqs hsum hUp hUup hUtight hUne hUlt ih'
    -- Strictly-feasible case: push flow.
    push Not at hT
    set slackf : Finset α → ℝ := fun U' => (∑ x ∈ U', q x) - (∑ x ∈ U', p x) with hslackdef
    set D := s.powerset.filter (fun U' => UpOn s U' ∧ a ∉ U' ∧ b ∈ U') with hDdef
    have hDmem : ∀ U', UpOn s U' → a ∉ U' → b ∈ U' → U' ∈ D := by
      intro U' hup ha' hb'
      rw [hDdef, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hup.1, hup, ha', hb'⟩
    -- Support-preservation facts (used to bound `M` after a push).
    have hple : ∀ t : ℝ, sp s (fun x => p x - if x = a then t else 0) ≤ sp s p :=
      fun t => sp_mono s p _ (fun x _ hx => by
        by_cases hxa : x = a
        · rw [hxa]; exact hpa
        · simpa [hxa] using hx)
    have hqle : ∀ t : ℝ, sp s (fun y => q y - if y = b then t else 0) ≤ sp s q :=
      fun t => sp_mono s q _ (fun y _ hy => by
        by_cases hyb : y = b
        · rw [hyb]; exact hqb
        · simpa [hyb] using hy)
    -- The push construction, given a valid `t`.
    have doPush : ∀ t : ℝ, 0 ≤ t → t ≤ p a → t ≤ q b →
        (∀ U', UpOn s U' → a ∉ U' → b ∈ U' → t ≤ (∑ x ∈ U', q x) - ∑ x ∈ U', p x) →
        (sp s (fun x => p x - if x = a then t else 0)
          + sp s (fun y => q y - if y = b then t else 0) < sp s p + sp s q) →
        Concl s p q := by
      intro t ht0 hta htb hslackH hdec
      have hpush := push_hyps s p q a b t hp hq hps hqs hsum hUp hab haS hbS ht0 hta htb hslackH
      have hMlt : M s (fun x => p x - if x = a then t else 0)
          (fun y => q y - if y = b then t else 0) < M s p q := M_push_lt s p q _ _ hdec
      exact push_concl s p q a b t hps hqs hab haS hbS ht0 (ih' _ _ _ hMlt hpush)
    by_cases hDne : D.Nonempty
    · obtain ⟨Us, hUsD, hUsmin⟩ := Finset.exists_min_image D slackf hDne
      rw [hDdef, Finset.mem_filter, Finset.mem_powerset] at hUsD
      obtain ⟨hUssub, hUsup, haUs, hbUs⟩ := hUsD
      have hslackU : ∀ U', UpOn s U' → a ∉ U' → b ∈ U' → slackf Us ≤ (∑ x ∈ U', q x) - ∑ x ∈ U', p
          x :=
        fun U' hup ha' hb' => hUsmin U' (hDmem U' hup ha' hb')
      by_cases htle : slackf Us < min (p a) (q b)
      · -- Push `t = slackf Us`, making `Us` tight, then split.
        have ht0 : 0 ≤ slackf Us := by rw [hslackdef]; simp only; linarith [hUp Us hUsup]
        have hta : slackf Us ≤ p a := le_of_lt (lt_of_lt_of_le htle (min_le_left _ _))
        have htb : slackf Us ≤ q b := le_of_lt (lt_of_lt_of_le htle (min_le_right _ _))
        have hpush := push_hyps s p q a b (slackf Us) hp hq hps hqs hsum hUp hab haS hbS
          ht0 hta htb hslackU
        obtain ⟨hp', hq', hps', hqs', hsum', hUp'⟩ := hpush
        have hpsum : ∀ T : Finset α, ∑ x ∈ T, (p x - if x = a then slackf Us else 0)
            = (∑ x ∈ T, p x) - (if a ∈ T then slackf Us else 0) := fun T => by
          simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq']
        have hqsum : ∀ T : Finset α, ∑ x ∈ T, (q x - if x = b then slackf Us else 0)
            = (∑ x ∈ T, q x) - (if b ∈ T then slackf Us else 0) := fun T => by
          simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq']
        have hUstight : ∑ x ∈ Us, (p x - if x = a then slackf Us else 0)
            = ∑ x ∈ Us, (q x - if x = b then slackf Us else 0) := by
          rw [hpsum Us, hqsum Us, ite_eq_right haUs, ite_eq_left hbUs, hslackdef]; simp only; ring
        have hMle : M s (fun x => p x - if x = a then slackf Us else 0)
            (fun y => q y - if y = b then slackf Us else 0) ≤ M s p q := by
          simp only [M]; have := hple (slackf Us); have := hqle (slackf Us); omega
        have ihSplit : ∀ (s'' : Finset α) (p'' q'' : α → ℝ),
            M s'' p'' q'' < M s (fun x => p x - if x = a then slackf Us else 0)
              (fun y => q y - if y = b then slackf Us else 0) → Hyps s'' p'' q'' → Concl s'' p''
                  q'' :=
          fun s'' p'' q'' hlt h => ih' s'' p'' q'' (lt_of_lt_of_le hlt hMle) h
        exact push_concl s p q a b (slackf Us) hps hqs hab haS hbS ht0
          (coupling_split s Us _ _ hp' hq' hps' hqs' hsum' hUp' hUsup hUstight ⟨b, hbUs⟩
            ((Finset.ssubset_iff_of_subset hUssub).mpr ⟨a, haS, haUs⟩) ihSplit)
      · -- Push `t = min (p a) (q b)`, reducing support.
        push Not at htle
        set t := min (p a) (q b) with htdef
        have ht0 : 0 ≤ t := le_min (le_of_lt hpa') (le_of_lt (lt_of_le_of_ne (hq b) (Ne.symm hqb)))
        have hslackH : ∀ U', UpOn s U' → a ∉ U' → b ∈ U' → t ≤ (∑ x ∈ U', q x) - ∑ x ∈ U', p x :=
          fun U' hup ha' hb' => le_trans htle
              (le_trans (by rw [hslackdef]) (hslackU U' hup ha' hb'))
        refine doPush t ht0 (min_le_left _ _) (min_le_right _ _) hslackH ?_
        by_cases hpq : p a ≤ q b
        · have hteq : t = p a := min_eq_left hpq
          have hzero : (fun x => p x - if x = a then t else 0) a = 0 := by
            change p a - (if a = a then t else 0) = 0; rw [ite_eq_left rfl, hteq]; ring
          have h1 := sp_lt s p (fun x => p x - if x = a then t else 0) a haS hpa hzero
              (fun x _ hx => by
            by_cases hxa : x = a
            · rw [hxa]; exact hpa
            · simpa [hxa] using hx)
          have h2 := hqle t
          omega
        · push Not at hpq
          have hteq : t = q b := min_eq_right (le_of_lt hpq)
          have hzero : (fun y => q y - if y = b then t else 0) b = 0 := by
            change q b - (if b = b then t else 0) = 0; rw [ite_eq_left rfl, hteq]; ring
          have h1 := sp_lt s q (fun y => q y - if y = b then t else 0) b hbS hqb hzero
              (fun y _ hy => by
            by_cases hyb : y = b
            · rw [hyb]; exact hqb
            · simpa [hyb] using hy)
          have h2 := hple t
          omega
    · -- No dangerous upper sets: push `t = min (p a) (q b)` safely.
      have hDempty : D = ∅ := Finset.not_nonempty_iff_eq_empty.1 hDne
      set t := min (p a) (q b) with htdef
      have ht0 : 0 ≤ t := le_min (le_of_lt hpa') (le_of_lt (lt_of_le_of_ne (hq b) (Ne.symm hqb)))
      have hslackH : ∀ U', UpOn s U' → a ∉ U' → b ∈ U' → t ≤ (∑ x ∈ U', q x) - ∑ x ∈ U', p x := by
        intro U' hup ha' hb'
        exact absurd (hDmem U' hup ha' hb') (by rw [hDempty]; exact Finset.notMem_empty U')
      refine doPush t ht0 (min_le_left _ _) (min_le_right _ _) hslackH ?_
      by_cases hpq : p a ≤ q b
      · have hteq : t = p a := min_eq_left hpq
        have hzero : (fun x => p x - if x = a then t else 0) a = 0 := by
          change p a - (if a = a then t else 0) = 0; rw [ite_eq_left rfl, hteq]; ring
        have h1 := sp_lt s p (fun x => p x - if x = a then t else 0) a haS hpa hzero
            (fun x _ hx => by
          by_cases hxa : x = a
          · rw [hxa]; exact hpa
          · simpa [hxa] using hx)
        have h2 := hqle t
        omega
      · push Not at hpq
        have hteq : t = q b := min_eq_right (le_of_lt hpq)
        have hzero : (fun y => q y - if y = b then t else 0) b = 0 := by
          change q b - (if b = b then t else 0) = 0; rw [ite_eq_left rfl, hteq]; ring
        have h1 := sp_lt s q (fun y => q y - if y = b then t else 0) b hbS hqb hzero
            (fun y _ hy => by
          by_cases hyb : y = b
          · rw [hyb]; exact hqb
          · simpa [hyb] using hy)
        have h2 := hple t
        omega

/-- Hard direction: the upper-set inequalities give a coupling. -/
private theorem exists_coupling_of_upper
    {α : Type*} [Fintype α] [PartialOrder α]
    (p q : α → ℝ)
    (hp_nonneg : ∀ x, 0 ≤ p x)
    (hq_nonneg : ∀ x, 0 ≤ q x)
    (hsum : ∑ x : α, p x = ∑ x : α, q x)
    (hUpper : ∀ U : Finset α, IsUpperSet U → ∑ x ∈ U, p x ≤ ∑ x ∈ U, q x) :
    ∃ π : α → α → ℝ,
      (∀ x y, 0 ≤ π x y) ∧
      (∀ x, ∑ y : α, π x y = p x) ∧
      (∀ y, ∑ x : α, π x y = q y) ∧
      (∀ x y, ¬ x ≤ y → π x y = 0) := by
  classical
  have hHyps : Hyps (Finset.univ : Finset α) p q := by
    refine ⟨hp_nonneg, hq_nonneg, ?_, ?_, hsum, ?_⟩
    · intro x hx; exact absurd (Finset.mem_univ x) hx
    · intro x hx; exact absurd (Finset.mem_univ x) hx
    · intro U hU
      refine hUpper U ?_
      intro x y hxU hxy
      exact hU.2 hxU (Finset.mem_univ y) hxy
  obtain ⟨π, hpos, hrow, hcol, hsupp, _⟩ :=
    exists_coupling_carrier (M (Finset.univ : Finset α) p q) Finset.univ p q (le_refl _) hHyps
  exact ⟨π, hpos, hrow, hcol, hsupp⟩

/-- **Strassen's theorem on a finite poset, equal-mass form.** Let $\alpha$ be a finite partially
ordered set and let $p, q : \alpha \to \mathbb{R}$ be nonnegative functions with
$\sum_{x \in \alpha} p(x) = \sum_{x \in \alpha} q(x)$. Then
$\sum_{x \in U} p(x) \le \sum_{x \in U} q(x)$ for every upper set $U \subseteq \alpha$ if and only
if there is a function $\pi : \alpha \times \alpha \to \mathbb{R}$ such that $\pi(x, y) \ge 0$
for all $x, y \in \alpha$, $\sum_{y \in \alpha} \pi(x, y) = p(x)$ for every $x \in \alpha$,
$\sum_{x \in \alpha} \pi(x, y) = q(y)$ for every $y \in \alpha$, and $\pi(x, y) = 0$ whenever
$x \not\le y$. -/
theorem forall_isUpperSet_sum_le_iff_exists_coupling
    {α : Type*} [Fintype α] [PartialOrder α]
    (p q : α → ℝ)
    (hp_nonneg : ∀ x, 0 ≤ p x)
    (hq_nonneg : ∀ x, 0 ≤ q x)
    (hsum : ∑ x : α, p x = ∑ x : α, q x) :
    (∀ U : Finset α, IsUpperSet U → ∑ x ∈ U, p x ≤ ∑ x ∈ U, q x) ↔
    ∃ π : α → α → ℝ,
      (∀ x y, 0 ≤ π x y) ∧
      (∀ x, ∑ y : α, π x y = p x) ∧
      (∀ y, ∑ x : α, π x y = q y) ∧
      (∀ x y, ¬ x ≤ y → π x y = 0) := by
  classical
  constructor
  · exact exists_coupling_of_upper p q hp_nonneg hq_nonneg hsum
  · rintro ⟨π, hpos, hrow, hcol, hsupp⟩ U hU
    have key : ∀ x ∈ U, p x = ∑ y ∈ U, π x y := by
      intro x hx
      rw [← hrow x]
      exact (Finset.sum_subset (Finset.subset_univ U)
        (fun y _ hyU => hsupp x y (fun hxy => hyU (hU hx hxy)))).symm
    calc ∑ x ∈ U, p x = ∑ x ∈ U, ∑ y ∈ U, π x y := Finset.sum_congr rfl key
      _ = ∑ y ∈ U, ∑ x ∈ U, π x y := Finset.sum_comm
      _ ≤ ∑ y ∈ U, q y := by
          apply Finset.sum_le_sum
          intro y _
          rw [← hcol y]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
            (fun x _ _ => hpos x y)


set_option linter.unusedDecidableInType false in
/--
**Strassen's theorem on a finite poset.** Let $\alpha$ be a finite partially ordered set and let
$p, q : \alpha \to \mathbb{R}$ be probability mass functions, that is, nonnegative functions with
$\sum_{x \in \alpha} p(x) = 1$ and $\sum_{x \in \alpha} q(x) = 1$. Then
$\sum_{x \in U} p(x) \le \sum_{x \in U} q(x)$ for every upper set $U \subseteq \alpha$ if and only
if there is a function $\pi : \alpha \times \alpha \to \mathbb{R}$ such that $\pi(x, y) \ge 0$
for all $x, y \in \alpha$, $\sum_{y \in \alpha} \pi(x, y) = p(x)$ for every $x \in \alpha$,
$\sum_{x \in \alpha} \pi(x, y) = q(y)$ for every $y \in \alpha$, and $\pi(x, y) = 0$ whenever
$x \not\le y$.

Proves `Wanted` entry `strassen_coupling_finite_poset`.

Source: V. Strassen, "The Existence of Probability Measures with Given Marginals", Ann. Math.
Statist. 36 (1965), 423-439, DOI 10.1214/aoms/1177700153.
-/
theorem strassen_coupling_finite_poset
    {α : Type*} [Fintype α] [PartialOrder α] [DecidableEq α]
    [DecidableLE α]
    (p q : α → ℝ)
    (hp_nonneg : ∀ x, 0 ≤ p x)
    (hq_nonneg : ∀ x, 0 ≤ q x)
    (hp_sum : ∑ x : α, p x = 1)
    (hq_sum : ∑ x : α, q x = 1) :
    (∀ U : Finset α, IsUpperSet U → ∑ x ∈ U, p x ≤ ∑ x ∈ U, q x) ↔
    ∃ π : α → α → ℝ,
      (∀ x y, 0 ≤ π x y) ∧
      (∀ x, ∑ y : α, π x y = p x) ∧
      (∀ y, ∑ x : α, π x y = q y) ∧
      (∀ x y, ¬ x ≤ y → π x y = 0) :=
  forall_isUpperSet_sum_le_iff_exists_coupling p q hp_nonneg hq_nonneg (by rw [hp_sum, hq_sum])

end MathlibExt.Probability.StrassenCouplingWanted
