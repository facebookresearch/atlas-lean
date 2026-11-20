/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































import Mathlib

namespace StatMech.Onsager.ChordCut

open scoped BigOperators




abbrev Pt := ℤ × ℤ



def cross (a b : Pt) : ℤ := a.1 * b.2 - a.2 * b.1


theorem cross_antisymm (a b : Pt) : cross a b = - cross b a := by
  simp only [cross]; ring


def isDir (d : Pt) : Prop :=
  d = (1, 0) ∨ d = (-1, 0) ∨ d = (0, 1) ∨ d = (0, -1)

instance (d : Pt) : Decidable (isDir d) := by unfold isDir; infer_instance





















theorem reflex_continuation_interior (din dout : Pt)
    (_hd : isDir din) (hrefl : cross din dout = -1) :
    cross din din = 0 ∧ 0 < cross dout din := by
  refine ⟨by simp [cross]; ring, ?_⟩
  have h := cross_antisymm din dout
  omega





theorem convex_continuation_exterior (din dout : Pt) (hconv : cross din dout = 1) :
    cross dout din < 0 := by
  have h := cross_antisymm din dout
  omega







theorem continuation_not_exterior (din : Pt) (hd : isDir din) :
    din.1 * (-din).1 + din.2 * (-din).2 < 0 := by
  rcases hd with h | h | h | h <;> subst h <;> decide










def rayX (w : Pt) (k : ℕ) : Pt := (w.1 + (k : ℤ), w.2)


structure BoxData where
  
  B : Finset Pt
  
  x1 : ℤ
  
  hx1 : ∀ p ∈ B, p.1 ≤ x1



def stopEvent (D : BoxData) (w : Pt) (k : ℕ) : Prop :=
  1 ≤ k ∧ (rayX w k ∈ D.B ∨ D.x1 < w.1 + (k : ℤ))

instance (D : BoxData) (w : Pt) (k : ℕ) : Decidable (stopEvent D w k) := by
  unfold stopEvent; infer_instance



theorem stopEvent_exists (D : BoxData) (w : Pt) (hw : w ∈ D.B) :
    ∃ k, stopEvent D w k := by
  refine ⟨(D.x1 - w.1 + 1).toNat, ?_, Or.inr ?_⟩
  · have : 1 ≤ D.x1 - w.1 + 1 := by have := D.hx1 w hw; omega
    omega
  · have hle := D.hx1 w hw
    have : ((D.x1 - w.1 + 1).toNat : ℤ) = D.x1 - w.1 + 1 := by
      rw [Int.toNat_of_nonneg]; omega
    omega









theorem chord_firstHit (D : BoxData) (w : Pt) (hw : w ∈ D.B) :
    ∃ k : ℕ, 1 ≤ k ∧ (rayX w k ∈ D.B ∨ D.x1 < w.1 + (k : ℤ)) ∧
      (∀ j : ℕ, 1 ≤ j → j < k → rayX w j ∉ D.B ∧ w.1 + (j : ℤ) ≤ D.x1) := by
  classical
  have hex : ∃ k, stopEvent D w k := stopEvent_exists D w hw
  refine ⟨Nat.find hex, ?_, ?_, ?_⟩
  · exact (Nat.find_spec hex).1
  · exact (Nat.find_spec hex).2
  · intro j hj1 hjk
    have hnot : ¬ stopEvent D w j := Nat.find_min hex hjk
    simp only [stopEvent, not_and, not_or, not_lt] at hnot
    have := hnot hj1
    exact ⟨this.1, this.2⟩











def chordInterior (w : Pt) (k : ℕ) : List Pt :=
  (List.range' 1 (k - 1)).map (rayX w)


theorem rayX_injective (w : Pt) : Function.Injective (rayX w) := by
  intro a b hab
  simp only [rayX, Prod.mk.injEq] at hab
  have : (a : ℤ) = (b : ℤ) := by omega
  exact_mod_cast this



theorem chordInterior_nodup (w : Pt) (k : ℕ) : (chordInterior w k).Nodup := by
  unfold chordInterior
  exact (List.nodup_range').map (rayX_injective w)




theorem chordInterior_disjoint_boundary (D : BoxData) (w : Pt) (k : ℕ) (arc : List Pt)
    (harc : ∀ p ∈ arc, p ∈ D.B)
    (hint : ∀ p ∈ chordInterior w k, p ∉ D.B) :
    arc.Disjoint (chordInterior w k) := by
  intro p hpa hpc
  exact hint p hpc (harc p hpa)




theorem chordInterior_offBoundary (D : BoxData) (w : Pt) (k : ℕ)
    (hfh : ∀ j : ℕ, 1 ≤ j → j < k → rayX w j ∉ D.B) :
    ∀ p ∈ chordInterior w k, p ∉ D.B := by
  intro p hp
  unfold chordInterior at hp
  rw [List.mem_map] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  rw [List.mem_range'] at hj
  obtain ⟨i, hik, rfl⟩ := hj
  exact hfh (1 + 1 * i) (by omega) (by omega)







theorem chord_piece_nodup (D : BoxData) (w : Pt) (k : ℕ) (arc : List Pt)
    (harcND : arc.Nodup) (harc : ∀ p ∈ arc, p ∈ D.B)
    (hint : ∀ p ∈ chordInterior w k, p ∉ D.B) :
    (arc ++ chordInterior w k).Nodup := by
  exact List.Nodup.append harcND (chordInterior_nodup w k)
    (chordInterior_disjoint_boundary D w k arc harc hint)

















def InteriorReaches (D : BoxData) (w : Pt) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ rayX w k ∈ D.B











theorem chord_of_interiorReaches (D : BoxData) (w : Pt) (_hw : w ∈ D.B)
    (hcore : InteriorReaches D w) :
    ∃ k : ℕ, 1 ≤ k ∧ rayX w k ∈ D.B ∧
      (∀ j : ℕ, 1 ≤ j → j < k → rayX w j ∉ D.B) := by
  classical
  
  have hex' : ∃ k, 1 ≤ k ∧ rayX w k ∈ D.B := hcore
  refine ⟨Nat.find hex', (Nat.find_spec hex').1, (Nat.find_spec hex').2, ?_⟩
  intro j hj1 hjk hjB
  exact Nat.find_min hex' hjk ⟨hj1, hjB⟩





theorem chord_split_of_core (D : BoxData) (w : Pt) (_hw : w ∈ D.B)
    (hcore : InteriorReaches D w) (arc : List Pt)
    (harcND : arc.Nodup) (harc : ∀ p ∈ arc, p ∈ D.B) :
    ∃ k : ℕ, 1 ≤ k ∧ rayX w k ∈ D.B ∧ (arc ++ chordInterior w k).Nodup := by
  obtain ⟨k, hk1, hkB, hoff⟩ := chord_of_interiorReaches D w _hw hcore
  refine ⟨k, hk1, hkB, ?_⟩
  exact chord_piece_nodup D w k arc harcND harc (chordInterior_offBoundary D w k hoff)
























































end StatMech.Onsager.ChordCut
