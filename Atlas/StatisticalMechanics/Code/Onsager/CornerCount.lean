/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















































import Mathlib
import Code.Onsager.WindingAssembly

namespace StatMech.Onsager.CornerCount

open StatMech.Onsager.WindingAssembly
open StatMech.Onsager.SplitConstruction


def bigSquare : List Pt := [(0, 0), (2, 0), (2, 2), (0, 2)]

theorem bigSquare_cc : ccCount bigSquare = 0 := by decide

theorem bigSquare_rc : rcCount bigSquare = 0 := by decide

theorem bigSquare_simple : simplePred bigSquare := by
  refine ⟨by decide, ?_, ?_⟩
  · 
    unfold bigSquare isAxisAligned
    refine List.IsChain.cons ?_ ?_
    refine List.IsChain.cons ?_ ?_
    refine List.IsChain.cons ?_ ?_
    · exact List.isChain_singleton _
    · intro y hy; simp at hy; subst hy; right; rfl
    · intro y hy; simp at hy; subst hy; left; rfl
    · intro y hy; simp at hy; subst hy; right; rfl
  · 
    intro x hx y hy
    simp only [bigSquare, List.getLast?, List.head?] at hx hy
    rw [Option.mem_some_iff] at hx hy
    subst hx; subst hy; left; rfl







theorem hbase_false :
    ¬ (∀ V : List Pt, simplePred V → rcCount V = 0 → ccCount V = 4) := by
  intro h
  have := h bigSquare bigSquare_simple bigSquare_rc
  rw [bigSquare_cc] at this
  exact absurd this (by decide)












theorem sum_eq_ccrc (L : List ℤ) (h : ∀ t ∈ L, t = -1 ∨ t = 0 ∨ t = 1) :
    L.sum = ((L.countP (fun t => t == 1) : ℕ) : ℤ) - ((L.countP (fun t => t == -1) : ℕ) : ℤ) := by
  induction L with
  | nil => simp
  | cons a t ih =>
    have hmem : ∀ x ∈ t, x = -1 ∨ x = 0 ∨ x = 1 := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have ha := h a (List.mem_cons_self ..)
    rw [List.sum_cons, List.countP_cons, List.countP_cons, ih hmem]
    rcases ha with ha | ha | ha <;> subst ha <;> push_cast <;> simp <;> ring


def cornerBalanceL (V : List Pt) : ℤ := (turnList V).sum



theorem cornerBalanceL_eq (V : List Pt)
    (h : ∀ t ∈ turnList V, t = -1 ∨ t = 0 ∨ t = 1) :
    cornerBalanceL V = ccCount V - rcCount V := by
  unfold cornerBalanceL ccCount rcCount
  exact sum_eq_ccrc (turnList V) h


theorem mem_zipWith_imp {α β γ : Type*} (f : α → β → γ) :
    ∀ (l₁ : List α) (l₂ : List β) (c : γ), c ∈ List.zipWith f l₁ l₂ →
      ∃ a b, a ∈ l₁ ∧ b ∈ l₂ ∧ c = f a b
  | [], _, c, hc => by simp at hc
  | _, [], c, hc => by simp at hc
  | a :: l₁, b :: l₂, c, hc => by
    rw [List.zipWith_cons_cons, List.mem_cons] at hc
    rcases hc with hc | hc
    · exact ⟨a, b, List.mem_cons_self .., List.mem_cons_self .., hc⟩
    · obtain ⟨a', b', ha', hb', hc'⟩ := mem_zipWith_imp f l₁ l₂ c hc
      exact ⟨a', b', List.mem_cons_of_mem _ ha', List.mem_cons_of_mem _ hb', hc'⟩


def stepList (V : List Pt) : List Pt :=
  List.zipWith (fun p q : Pt => ((q.1 - p.1 : ℤ), (q.2 - p.2 : ℤ))) V (V.rotate 1)


theorem turnList_eq (V : List Pt) :
    turnList V = List.zipWith turn (stepList V) ((stepList V).rotate 1) := rfl




theorem turnList_bounded (V : List Pt)
    (hunit : ∀ d ∈ stepList V, StatMech.Onsager.PolygonWalk.isUnitDir d) :
    ∀ t ∈ turnList V, t = -1 ∨ t = 0 ∨ t = 1 := by
  intro t ht
  rw [turnList_eq] at ht
  obtain ⟨a, b, ha, hb, hc⟩ := mem_zipWith_imp turn (stepList V) ((stepList V).rotate 1) t ht
  have hb' : b ∈ stepList V := (List.mem_rotate).1 hb
  have := StatMech.Onsager.PolygonWalk.cross_unit_mem a b (hunit a ha) (hunit b hb')
  rw [hc]; exact this



theorem cornerBalanceL_eq_of_unit (V : List Pt)
    (hunit : ∀ d ∈ stepList V, StatMech.Onsager.PolygonWalk.isUnitDir d) :
    cornerBalanceL V = ccCount V - rcCount V :=
  cornerBalanceL_eq V (turnList_bounded V hunit)










theorem balanceL_split_of_counts (V : List Pt) (a b : ℕ)
    (hbV : ∀ t ∈ turnList V, t = -1 ∨ t = 0 ∨ t = 1)
    (hbA : ∀ t ∈ turnList (arc V a b), t = -1 ∨ t = 0 ∨ t = 1)
    (hbC : ∀ t ∈ turnList (coarc V a b), t = -1 ∨ t = 0 ∨ t = 1)
    (hcc : ccCount (arc V a b) + ccCount (coarc V a b) = ccCount V + 3)
    (hrc : rcCount (arc V a b) + rcCount (coarc V a b) = rcCount V - 1) :
    cornerBalanceL V = cornerBalanceL (arc V a b) + cornerBalanceL (coarc V a b) - 4 := by
  rw [cornerBalanceL_eq V hbV, cornerBalanceL_eq (arc V a b) hbA,
    cornerBalanceL_eq (coarc V a b) hbC]
  omega

end StatMech.Onsager.CornerCount
