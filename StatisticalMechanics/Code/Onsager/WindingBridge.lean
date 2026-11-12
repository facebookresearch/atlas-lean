/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































import Mathlib
import Code.Onsager.InteriorReaches
import Code.Lattice.CrossingParity

namespace StatMech.Onsager.WindingBridge

open StatMech.Lattice
open StatMech.Onsager.ChordCut
open StatMech.Onsager.InteriorReaches




def toSite (p : Pt) : Site 2 := ![p.1, p.2]

@[simp] theorem toSite_zero (p : Pt) : toSite p 0 = p.1 := by simp [toSite]
@[simp] theorem toSite_one (p : Pt) : toSite p 1 = p.2 := by simp [toSite]


theorem toSite_injective : Function.Injective toSite := by
  intro a b h
  have h0 : toSite a 0 = toSite b 0 := by rw [h]
  have h1 : toSite a 1 = toSite b 1 := by rw [h]
  simp only [toSite_zero, toSite_one] at h0 h1
  exact Prod.ext h0 h1


theorem shift_injective : Function.Injective (fun p : Pt => (p.1 + 1, p.2)) := by
  intro a b h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (by omega) h.2



theorem toSite_adj_shift (p : Pt) :
    (hypercubicLattice 2).Adj (toSite p) (toSite (p.1 + 1, p.2)) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simp only [toSite_zero, toSite_one]
  omega








theorem barrier_of_side_change (S : Set (Site 2)) {x y : Site 2}
    (hadj : (hypercubicLattice 2).Adj x y) (hchg : ¬ (x ∈ S ↔ y ∈ S)) :
    bdEdge S s(x, y) := by
  by_contra hnb
  have hadj' : (latticeMinusBarrier S).Adj x y := ⟨hadj, hnb⟩
  exact hchg (latticeMinusBarrier_sameSide S hadj'.toWalk)




def preS (S : Set (Site 2)) : Set Pt := {p : Pt | toSite p ∈ S}


theorem preS_finite (S : Set (Site 2)) (hfin : S.Finite) : (preS S).Finite :=
  Set.Finite.preimage (toSite_injective.injOn) hfin



theorem shiftPre_finite (S : Set (Site 2)) (hfin : S.Finite) :
    {p : Pt | toSite (p.1 + 1, p.2) ∈ S}.Finite :=
  Set.Finite.preimage ((toSite_injective.comp shift_injective).injOn) hfin



def Bset (S : Set (Site 2)) : Set Pt :=
  {p : Pt | bdEdge S s(toSite p, toSite (p.1 + 1, p.2))}



theorem bset_subset (S : Set (Site 2)) :
    Bset S ⊆ preS S ∪ {p : Pt | toSite (p.1 + 1, p.2) ∈ S} := by
  intro p hp
  rw [Bset, Set.mem_setOf_eq, bdEdge_mk] at hp
  by_cases h : toSite p ∈ S
  · exact Or.inl h
  · refine Or.inr ?_
    by_contra hc
    exact h (hp.mpr hc)


theorem bset_finite (S : Set (Site 2)) (hfin : S.Finite) : (Bset S).Finite :=
  ((preS_finite S hfin).union (shiftPre_finite S hfin)).subset (bset_subset S)




noncomputable def xBound (S : Set (Site 2)) (hfin : S.Finite) : ℤ :=
  (hfin.image (fun x : Site 2 => x 0)).bddAbove.choose


theorem le_xBound (S : Set (Site 2)) (hfin : S.Finite) {x : Site 2} (hx : x ∈ S) :
    x 0 ≤ xBound S hfin :=
  (hfin.image (fun x : Site 2 => x 0)).bddAbove.choose_spec ⟨x, hx, rfl⟩





noncomputable def mkBoxData (S : Set (Site 2)) (hfin : S.Finite) : BoxData where
  B := (bset_finite S hfin).toFinset
  x1 := xBound S hfin
  hx1 := by
    intro p hp
    rw [Set.Finite.mem_toFinset] at hp
    rcases bset_subset S hp with h | h
    · have hle := le_xBound S hfin (show toSite p ∈ S from h)
      simpa using hle
    · have hle := le_xBound S hfin (show toSite (p.1 + 1, p.2) ∈ S from h)
      have he : toSite (p.1 + 1, p.2) 0 = p.1 + 1 := by simp
      rw [he] at hle
      omega



theorem boundedRight (S : Set (Site 2)) (hfin : S.Finite) :
    BoundedRight (mkBoxData S hfin) (preS S) := by
  intro p hp
  have hle := le_xBound S hfin (show toSite p ∈ S from hp)
  simpa [mkBoxData] using hle






theorem boundaryCovers (S : Set (Site 2)) (hfin : S.Finite) :
    BoundaryCoversTransitions (mkBoxData S hfin) (preS S) := by
  intro p hne
  refine Or.inl ?_
  have hchg : ¬ (toSite p ∈ S ↔ toSite (p.1 + 1, p.2) ∈ S) := hne
  have hbd := barrier_of_side_change S (toSite_adj_shift p) hchg
  show p ∈ (bset_finite S hfin).toFinset
  rw [Set.Finite.mem_toFinset]
  exact hbd














theorem interiorReaches_of_cluster (S : Set (Site 2)) (hfin : S.Finite) (w : Pt)
    (hin : toSite (rayX w 1) ∈ S) :
    InteriorReaches (mkBoxData S hfin) w :=
  interiorReaches_of_polygon (mkBoxData S hfin) w (preS S)
    (boundedRight S hfin) (boundaryCovers S hfin) hin




theorem chord_of_cluster (S : Set (Site 2)) (hfin : S.Finite) (w : Pt)
    (hw : w ∈ (mkBoxData S hfin).B) (hin : toSite (rayX w 1) ∈ S) :
    ∃ k : ℕ, 1 ≤ k ∧ rayX w k ∈ (mkBoxData S hfin).B ∧
      (∀ j : ℕ, 1 ≤ j → j < k → rayX w j ∉ (mkBoxData S hfin).B) :=
  chord_of_interiorReaches (mkBoxData S hfin) w hw (interiorReaches_of_cluster S hfin w hin)

end StatMech.Onsager.WindingBridge
