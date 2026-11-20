/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Mathlib
import Code.Onsager.GroundUpWinding
import Code.Onsager.SplitConstruction
import Code.Onsager.PolygonWalk

namespace StatMech.Onsager.WindingAssembly

open StatMech.Onsager.SplitConstruction




def turn (p q : Pt) : ℤ := StatMech.Onsager.PolygonWalk.cross p q



def turnList (V : List Pt) : List ℤ :=
  let d := List.zipWith (fun p q : Pt => ((q.1 - p.1 : ℤ), (q.2 - p.2 : ℤ))) V (V.rotate 1)
  List.zipWith turn d (d.rotate 1)


def ccCount (V : List Pt) : ℤ := ((turnList V).countP (fun t => t == 1) : ℤ)


def rcCount (V : List Pt) : ℤ := ((turnList V).countP (fun t => t == -1) : ℤ)


def simplePred (V : List Pt) : Prop := V.Nodup ∧ IsClosedWalk isAxisAligned V


theorem isAxisAligned_symm {p q : Pt} (h : isAxisAligned p q) : isAxisAligned q p := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm


theorem ccCount_nonneg (V : List Pt) : 0 ≤ ccCount V := Int.natCast_nonneg _


theorem rcCount_nonneg (V : List Pt) : 0 ≤ rcCount V := Int.natCast_nonneg _













theorem structural_chord (V : List Pt) (a b : ℕ)
    (hnd : V.Nodup) (hchain : List.IsChain isAxisAligned V)
    (hwrap : ∀ x ∈ V.getLast?, ∀ y ∈ V.head?, isAxisAligned x y)
    (ha : a < V.length) (hb : b < V.length) (hab : a + 1 < b)
    (hstrict : 0 < a ∨ b + 1 < V.length)
    (hchord : isAxisAligned V[a] V[b]) :
    simplePred (arc V a b) ∧ simplePred (coarc V a b) ∧
      (arc V a b).length < V.length ∧ (coarc V a b).length < V.length := by
  refine ⟨⟨arc_nodup V a b hnd, ?_⟩, ⟨coarc_nodup V a b hnd (by omega), ?_⟩,
    arc_length_lt V a b hb (by omega) hstrict, coarc_length_lt V a b hb hab⟩
  · exact arc_isClosedWalk V a b hb (by omega) hchain (isAxisAligned_symm hchord)
  · exact coarc_isClosedWalk V a b hb (by omega) hchain hwrap hchord










theorem getElem!_eq_getElem (V : List Pt) (a : ℕ) (h : a < V.length) : V[a]! = V[a] := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl












def concretePolyData
    (hbase : ∀ V : List Pt, simplePred V → rcCount V = 0 → ccCount V = 4)
    (hchord : ∀ V : List Pt, simplePred V → 0 < rcCount V →
        ∃ a b : ℕ, a + 1 < b ∧ b < V.length ∧ (0 < a ∨ b + 1 < V.length) ∧
          isAxisAligned V[a]! V[b]! ∧
          ccCount (arc V a b) + ccCount (coarc V a b) = ccCount V + 3 ∧
          rcCount (arc V a b) + rcCount (coarc V a b) = rcCount V - 1) :
    StatMech.Onsager.GroundUp.RectPolygonData where
  Poly := List Pt
  size := List.length
  cc := ccCount
  rc := rcCount
  simple := simplePred
  hcc := fun P => ccCount_nonneg P
  hrc := fun P => rcCount_nonneg P
  base := hbase
  chord := by
    intro V hV hr
    obtain ⟨a, b, hab, hb, hstrict, hchd, hcceq, hrceq⟩ := hchord V hV hr
    have ha : a < V.length := by omega
    rw [getElem!_eq_getElem V a ha, getElem!_eq_getElem V b hb] at hchd
    obtain ⟨hs1, hs2, hlt1, hlt2⟩ :=
      structural_chord V a b hV.1 hV.2.1 hV.2.2 ha hb hab hstrict hchd
    exact ⟨arc V a b, coarc V a b, hs1, hs2, hlt1, hlt2, hcceq, hrceq⟩






theorem propIV_conditional
    (hbase : ∀ V : List Pt, simplePred V → rcCount V = 0 → ccCount V = 4)
    (hchord : ∀ V : List Pt, simplePred V → 0 < rcCount V →
        ∃ a b : ℕ, a + 1 < b ∧ b < V.length ∧ (0 < a ∨ b + 1 < V.length) ∧
          isAxisAligned V[a]! V[b]! ∧
          ccCount (arc V a b) + ccCount (coarc V a b) = ccCount V + 3 ∧
          rcCount (arc V a b) + rcCount (coarc V a b) = rcCount V - 1)
    (V : List Pt) (hV : simplePred V) :
    ccCount V - rcCount V = 4 :=
  (concretePolyData hbase hchord).umlaufsatz V hV

end StatMech.Onsager.WindingAssembly
