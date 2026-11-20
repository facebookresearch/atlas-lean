/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib























namespace StatMech.Onsager.SplitConstruction

open List

abbrev Pt := ℤ × ℤ


def isAxisAligned (p q : Pt) : Prop := p.1 = q.1 ∨ p.2 = q.2


def isUnitStep (p q : Pt) : Prop := (p.1 - q.1).natAbs + (p.2 - q.2).natAbs = 1




def IsClosedWalk (R : Pt → Pt → Prop) (L : List Pt) : Prop :=
  List.IsChain R L ∧ ∀ x ∈ L.getLast?, ∀ y ∈ L.head?, R x y



def arc (V : List Pt) (a b : ℕ) : List Pt := (V.drop a).take (b - a + 1)


def coarc (V : List Pt) (a b : ℕ) : List Pt := V.drop b ++ V.take (a + 1)



theorem arc_length (V : List Pt) (a b : ℕ) (hb : b < V.length) (hab : a ≤ b) :
    (arc V a b).length = b - a + 1 := by
  unfold arc
  rw [List.length_take, List.length_drop]
  omega

theorem coarc_length (V : List Pt) (a b : ℕ) (hb : b < V.length) (hab : a < b) :
    (coarc V a b).length = V.length - b + a + 1 := by
  unfold coarc
  rw [List.length_append, List.length_drop, List.length_take]
  omega



theorem split_length (V : List Pt) (a b : ℕ) (hb : b < V.length) (hab : a < b) :
    (arc V a b).length + (coarc V a b).length = V.length + 2 := by
  rw [arc_length V a b hb (le_of_lt hab), coarc_length V a b hb hab]
  omega



theorem arc_length_lt (V : List Pt) (a b : ℕ) (hb : b < V.length) (hab : a < b)
    (hstrict : 0 < a ∨ b + 1 < V.length) :
    (arc V a b).length < V.length := by
  rw [arc_length V a b hb (le_of_lt hab)]
  omega


theorem coarc_length_lt (V : List Pt) (a b : ℕ) (hb : b < V.length) (hab : a + 1 < b) :
    (coarc V a b).length < V.length := by
  rw [coarc_length V a b hb (by omega)]
  omega





theorem arc_nodup (V : List Pt) (a b : ℕ) (h : V.Nodup) : (arc V a b).Nodup := by
  unfold arc
  exact h.sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))



theorem coarc_disjoint (V : List Pt) (a b : ℕ) (h : V.Nodup) (hab : a < b) :
    ∀ x ∈ V.drop b, ∀ y ∈ V.take (a + 1), x ≠ y := by
  have hd : ∀ x ∈ V.take (a + 1), ∀ y ∈ V.drop (a + 1), x ≠ y := by
    have hV : (V.take (a + 1) ++ V.drop (a + 1)).Nodup := by
      rw [List.take_append_drop]; exact h
    exact (List.nodup_append.mp hV).2.2
  have hsub : V.drop b ⊆ V.drop (a + 1) := by
    have he : V.drop b = (V.drop (a + 1)).drop (b - (a + 1)) := by
      rw [List.drop_drop]; congr 1; omega
    rw [he]; exact List.drop_subset _ _
  intro x hx y hy
  exact (hd y hy x (hsub hx)).symm



theorem coarc_nodup (V : List Pt) (a b : ℕ) (h : V.Nodup) (hab : a < b) :
    (coarc V a b).Nodup := by
  unfold coarc
  rw [List.nodup_append]
  exact ⟨h.sublist (List.drop_sublist _ _), h.sublist (List.take_sublist _ _),
    coarc_disjoint V a b h hab⟩






theorem arc_head? (V : List Pt) (a b : ℕ) (hab : a ≤ b) :
    (arc V a b).head? = V[a]? := by
  unfold arc
  rw [List.head?_eq_getElem?, List.getElem?_take_of_lt (show (0:ℕ) < b - a + 1 by omega),
    List.getElem?_drop, Nat.add_zero]

theorem arc_getLast? (V : List Pt) (a b : ℕ) (hb : b < V.length) (hab : a ≤ b) :
    (arc V a b).getLast? = V[b]? := by
  unfold arc
  rw [List.getLast?_take, if_neg (show ¬ (b - a + 1 = 0) by omega),
    show b - a + 1 - 1 = b - a by omega, List.getElem?_drop,
    show a + (b - a) = b by omega, List.getElem?_eq_getElem hb, Option.some_or]

theorem coarc_head? (V : List Pt) (a b : ℕ) (hb : b < V.length) :
    (coarc V a b).head? = V[b]? := by
  unfold coarc
  rw [List.head?_append, List.head?_drop, List.getElem?_eq_getElem hb, Option.some_or]

theorem coarc_getLast? (V : List Pt) (a b : ℕ) (ha : a < V.length) :
    (coarc V a b).getLast? = V[a]? := by
  unfold coarc
  rw [List.getLast?_append, List.getLast?_take, if_neg (show ¬ (a + 1 = 0) by omega),
    show a + 1 - 1 = a by omega, List.getElem?_eq_getElem ha]
  simp only [Option.some_or]




theorem arc_isClosedWalk (V : List Pt) (a b : ℕ) (hb : b < V.length) (hab : a ≤ b)
    (hV : List.IsChain isAxisAligned V)
    (hchord : isAxisAligned V[b] V[a]) :
    IsClosedWalk isAxisAligned (arc V a b) := by
  refine ⟨?_, ?_⟩
  · 
    exact (hV.drop a).take (b - a + 1)
  · 
    rw [arc_getLast? V a b hb hab, arc_head? V a b hab,
      List.getElem?_eq_getElem hb, List.getElem?_eq_getElem (lt_of_le_of_lt hab hb)]
    intro x hx y hy
    rw [Option.mem_some_iff] at hx hy
    subst hx; subst hy
    exact hchord





theorem coarc_isClosedWalk (V : List Pt) (a b : ℕ) (hb : b < V.length) (hab : a < b)
    (hV : List.IsChain isAxisAligned V)
    (hVwrap : ∀ x ∈ V.getLast?, ∀ y ∈ V.head?, isAxisAligned x y)
    (hchord : isAxisAligned V[a] V[b]) :
    IsClosedWalk isAxisAligned (coarc V a b) := by
  have ha : a < V.length := lt_trans hab hb
  refine ⟨?_, ?_⟩
  · 
    refine List.IsChain.append (hV.drop b) (hV.take (a + 1)) ?_
    
    intro x hx y hy
    rw [List.getLast?_drop, if_neg (show ¬ (V.length ≤ b) by omega)] at hx
    rw [List.head?_take, if_neg (show ¬ (a + 1 = 0) by omega)] at hy
    exact hVwrap x hx y hy
  · 
    rw [coarc_getLast? V a b ha, coarc_head? V a b hb,
      List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb]
    intro x hx y hy
    rw [Option.mem_some_iff] at hx hy
    subst hx; subst hy
    exact hchord

end StatMech.Onsager.SplitConstruction
