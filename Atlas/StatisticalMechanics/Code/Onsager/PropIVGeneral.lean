/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib
import Code.Onsager.WindingBridge
import Code.Onsager.InteriorRegion
import Code.Onsager.ChordCut
import Code.Lattice.CrossingParity

namespace StatMech.Onsager.PropIVGeneral

open StatMech.Lattice
open StatMech.Onsager.ChordCut
open StatMech.Onsager.InteriorReaches
open StatMech.Onsager.WindingBridge
open StatMech.Onsager.InteriorRegion




def fromSite (x : Site 2) : Pt := (x 0, x 1)

@[simp] theorem fromSite_toSite (p : Pt) : fromSite (toSite p) = p := by
  simp only [fromSite, toSite_zero, toSite_one]

@[simp] theorem toSite_fromSite (x : Site 2) : toSite (fromSite x) = x := by
  funext i; fin_cases i <;> simp [toSite, fromSite]






abbrev Polygon := Finset Pt



def rayCross (Q : Polygon) (p : Pt) : ℕ :=
  (Q.filter (fun q => q.2 = p.2 ∧ p.1 ≤ q.1)).card



def leftCross (Q : Polygon) (p : Pt) : ℕ :=
  (Q.filter (fun q => q.2 = p.2 ∧ q.1 < p.1)).card



def rowCount (Q : Polygon) (y : ℤ) : ℕ :=
  (Q.filter (fun q => q.2 = y)).card



def IsClosedPolygon (Q : Polygon) : Prop := ∀ y : ℤ, Even (rowCount Q y)



def interiorSet (Q : Polygon) : Set (Site 2) := {x : Site 2 | Odd (rayCross Q (fromSite x))}


def preInterior (Q : Polygon) : Set Pt := {p : Pt | Odd (rayCross Q p)}

@[simp] theorem mem_interiorSet (Q : Polygon) (p : Pt) :
    toSite p ∈ interiorSet Q ↔ Odd (rayCross Q p) := by
  simp only [interiorSet, Set.mem_setOf_eq, fromSite_toSite]

theorem interiorSet_eq_image (Q : Polygon) : interiorSet Q = toSite '' preInterior Q := by
  ext x
  constructor
  · intro hx
    exact ⟨fromSite x, hx, toSite_fromSite x⟩
  · rintro ⟨p, hp, rfl⟩
    rw [mem_interiorSet]; exact hp





theorem rayCross_shift (Q : Polygon) (p : Pt) :
    rayCross Q (p.1 + 1, p.2) = (Q.filter (fun q => q.2 = p.2 ∧ p.1 + 1 ≤ q.1)).card := rfl




theorem rayCross_step (Q : Polygon) (p : Pt) :
    rayCross Q p = (if p ∈ Q then 1 else 0) + rayCross Q (p.1 + 1, p.2) := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
      (s := Q.filter (fun q => q.2 = p.2 ∧ p.1 ≤ q.1)) (p := fun q => q.1 = p.1)
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  
  have e1 : Q.filter (fun q => (q.2 = p.2 ∧ p.1 ≤ q.1) ∧ q.1 = p.1)
      = Q.filter (fun q => q = p) := by
    apply Finset.filter_congr
    intro q _
    constructor
    · rintro ⟨⟨h2, _⟩, h1⟩; exact Prod.ext h1 h2
    · rintro rfl; exact ⟨⟨rfl, le_refl _⟩, rfl⟩
  have e2 : Q.filter (fun q => (q.2 = p.2 ∧ p.1 ≤ q.1) ∧ ¬ q.1 = p.1)
      = Q.filter (fun q => q.2 = p.2 ∧ p.1 + 1 ≤ q.1) := by
    apply Finset.filter_congr
    intro q _
    constructor
    · rintro ⟨⟨h2, hle⟩, hne⟩; exact ⟨h2, by omega⟩
    · rintro ⟨h2, hle⟩; exact ⟨⟨h2, by omega⟩, by omega⟩
  rw [e1, e2, Finset.filter_eq'] at hsplit
  rw [rayCross, ← hsplit, rayCross_shift]
  by_cases hpQ : p ∈ Q <;> simp [hpQ]



theorem rayCross_add_leftCross (Q : Polygon) (p : Pt) :
    rayCross Q p + leftCross Q p = rowCount Q p.2 := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
      (s := Q.filter (fun q => q.2 = p.2)) (p := fun q => p.1 ≤ q.1)
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  have e1 : Q.filter (fun q => q.2 = p.2 ∧ p.1 ≤ q.1)
      = Q.filter (fun q => q.2 = p.2 ∧ p.1 ≤ q.1) := rfl
  have e2 : Q.filter (fun q => q.2 = p.2 ∧ ¬ p.1 ≤ q.1)
      = Q.filter (fun q => q.2 = p.2 ∧ q.1 < p.1) := by
    apply Finset.filter_congr; intro q _
    constructor
    · rintro ⟨h2, hle⟩; exact ⟨h2, by omega⟩
    · rintro ⟨h2, hle⟩; exact ⟨h2, by omega⟩
  rw [e1, e2] at hsplit
  rw [rayCross, leftCross, rowCount, hsplit]








theorem Bset_interiorSet (Q : Polygon) : Bset (interiorSet Q) = (↑Q : Set Pt) := by
  ext p
  rw [Bset, Set.mem_setOf_eq, bdEdge_mk, mem_interiorSet, mem_interiorSet, Finset.mem_coe]
  
  have hstep := rayCross_step Q p
  by_cases hpQ : p ∈ Q
  · rw [if_pos hpQ] at hstep
    have hb : rayCross Q p = rayCross Q (p.1 + 1, p.2) + 1 := by omega
    simp only [hpQ, iff_true]
    rw [hb, Nat.odd_add_one]
  · rw [if_neg hpQ] at hstep
    have hb : rayCross Q p = rayCross Q (p.1 + 1, p.2) := by omega
    simp only [hpQ, iff_false]
    rw [hb]
    tauto




theorem trap_finite (a b c : ℤ) : {p : Pt | a < p.1 ∧ p.1 ≤ b ∧ p.2 = c}.Finite := by
  apply Set.Finite.subset ((Set.finite_Ioc a b).image (fun x => (x, c)))
  rintro p ⟨h1, h2, h3⟩
  exact ⟨p.1, ⟨h1, h2⟩, Prod.ext rfl h3.symm⟩






theorem preInterior_finite (Q : Polygon) (hcl : IsClosedPolygon Q) : (preInterior Q).Finite := by
  classical
  apply Set.Finite.subset
    (s := ⋃ qL ∈ (↑Q : Set Pt), ⋃ qR ∈ (↑Q : Set Pt),
      {p : Pt | qL.1 < p.1 ∧ p.1 ≤ qR.1 ∧ p.2 = qR.2})
  · exact Set.Finite.biUnion Q.finite_toSet
      (fun qL _ => Set.Finite.biUnion Q.finite_toSet (fun qR _ => trap_finite qL.1 qR.1 qR.2))
  · intro p hp
    have hodd : Odd (rayCross Q p) := hp
    
    have hposR : 0 < rayCross Q p := by have := Nat.odd_iff.mp hodd; omega
    obtain ⟨qR, hqR⟩ := Finset.card_pos.mp hposR
    rw [Finset.mem_filter] at hqR
    obtain ⟨hqRQ, hqR2, hqR1⟩ := hqR
    
    have hrow := rayCross_add_leftCross Q p
    have hEven : Even (rowCount Q p.2) := hcl p.2
    have hoddL : Odd (leftCross Q p) := by
      rcases Nat.even_or_odd (leftCross Q p) with h | h
      · exfalso
        have := Nat.even_iff.mp hEven
        have := Nat.odd_iff.mp hodd
        have := Nat.even_iff.mp h
        omega
      · exact h
    have hposL : 0 < leftCross Q p := by have := Nat.odd_iff.mp hoddL; omega
    obtain ⟨qL, hqL⟩ := Finset.card_pos.mp hposL
    rw [Finset.mem_filter] at hqL
    obtain ⟨hqLQ, hqL2, hqL1⟩ := hqL
    
    refine Set.mem_biUnion (Finset.mem_coe.mpr hqLQ)
      (Set.mem_biUnion (Finset.mem_coe.mpr hqRQ) ?_)
    exact ⟨hqL1, hqR1, hqR2.symm⟩



theorem interior_finite (Q : Polygon) (hcl : IsClosedPolygon Q) : (interiorSet Q).Finite := by
  rw [interiorSet_eq_image]
  exact (preInterior_finite Q hcl).image toSite







theorem rayCast_parity (Q : Polygon) (p : Pt) (N : ℕ)
    (hout : toSite (rayX p N) ∉ interiorSet Q) :
    toSite p ∈ interiorSet Q ↔ ¬ Even (crossCount (interiorSet Q) (rayWalk p N)) :=
  interior_iff_odd_crossing (interiorSet Q) p N hout














theorem chord_general (Q : Polygon) (hcl : IsClosedPolygon Q) (w : Pt)
    (hw : w ∈ Q) (hlaunch : Odd (rayCross Q (w.1 + 1, w.2))) :
    ∃ k : ℕ, 1 ≤ k ∧ rayX w k ∈ (mkBoxData (interiorSet Q) (interior_finite Q hcl)).B ∧
      (∀ j : ℕ, 1 ≤ j → j < k →
        rayX w j ∉ (mkBoxData (interiorSet Q) (interior_finite Q hcl)).B) := by
  apply chord_of_cluster (interiorSet Q) (interior_finite Q hcl) w
  · 
    rw [mkBoxData, Set.Finite.mem_toFinset]
    show w ∈ Bset (interiorSet Q)
    rw [Bset_interiorSet]
    exact Finset.mem_coe.mpr hw
  · 
    have hr : rayX w 1 = (w.1 + 1, w.2) := by simp [rayX]
    rw [hr, mem_interiorSet]
    exact hlaunch





theorem interiorReaches_general (Q : Polygon) (hcl : IsClosedPolygon Q) (w : Pt)
    (hlaunch : Odd (rayCross Q (w.1 + 1, w.2))) :
    InteriorReaches (mkBoxData (interiorSet Q) (interior_finite Q hcl)) w := by
  apply interiorReaches_of_cluster (interiorSet Q) (interior_finite Q hcl) w
  have hr : rayX w 1 = (w.1 + 1, w.2) := by simp [rayX]
  rw [hr, mem_interiorSet]
  exact hlaunch











































end StatMech.Onsager.PropIVGeneral
