/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































import Mathlib
import Code.Onsager.ChordCut

namespace StatMech.Onsager.InteriorReaches

open StatMech.Onsager.ChordCut
open scoped BigOperators






def BoundedRight (D : BoxData) (S : Set Pt) : Prop :=
  ∀ p : Pt, p ∈ S → p.1 ≤ D.x1











def SeparatedBy (D : BoxData) (S : Set Pt) : Prop :=
  ∀ p : Pt, p ∉ D.B → (p.1 + 1, p.2) ∉ D.B → (p ∈ S ↔ (p.1 + 1, p.2) ∈ S)






def BoundaryCoversTransitions (D : BoxData) (S : Set Pt) : Prop :=
  ∀ p : Pt, ¬ (p ∈ S ↔ (p.1 + 1, p.2) ∈ S) → (p ∈ D.B ∨ (p.1 + 1, p.2) ∈ D.B)




theorem separatedBy_of_covers (D : BoxData) (S : Set Pt)
    (h : BoundaryCoversTransitions D S) : SeparatedBy D S := by
  intro p hpB hpB'
  by_contra hne
  rcases h p hne with h1 | h1
  · exact hpB h1
  · exact hpB' h1





theorem shift_ray (w : Pt) (k : ℕ) :
    ((rayX w k).1 + 1, (rayX w k).2) = rayX w (k + 1) := by
  simp only [rayX]
  refine Prod.ext_iff.mpr ⟨?_, ?_⟩
  · show w.1 + (k : ℤ) + 1 = w.1 + ((k + 1 : ℕ) : ℤ)
    push_cast; ring
  · rfl












theorem interiorReaches_of_separated (D : BoxData) (w : Pt) (S : Set Pt)
    (hbd : BoundedRight D S) (hsep : SeparatedBy D S) (hin : rayX w 1 ∈ S) :
    InteriorReaches D w := by
  by_contra hcon
  
  unfold InteriorReaches at hcon
  push Not at hcon
  have hoff : ∀ k : ℕ, 1 ≤ k → rayX w k ∉ D.B := hcon
  
  have hall : ∀ k : ℕ, rayX w (k + 1) ∈ S := by
    intro k
    induction k with
    | zero => simpa using hin
    | succ m ih =>
      have hpt : ((rayX w (m + 1)).1 + 1, (rayX w (m + 1)).2) = rayX w (m + 1 + 1) :=
        shift_ray w (m + 1)
      have hnbL : rayX w (m + 1) ∉ D.B := hoff (m + 1) (by omega)
      have hnbR : ((rayX w (m + 1)).1 + 1, (rayX w (m + 1)).2) ∉ D.B := by
        rw [hpt]; exact hoff (m + 1 + 1) (by omega)
      have hstep := (hsep (rayX w (m + 1)) hnbL hnbR).mp ih
      rwa [hpt] at hstep
  
  obtain ⟨n, hbig⟩ : ∃ n : ℕ, D.x1 < w.1 + ((n : ℤ) + 1) :=
    ⟨(D.x1 - w.1).toNat, by omega⟩
  have hInS := hall n
  have hle := hbd _ hInS
  simp only [rayX] at hle
  push_cast at hle hbig
  omega






theorem interiorReaches_of_polygon (D : BoxData) (w : Pt) (S : Set Pt)
    (hbd : BoundedRight D S) (hcov : BoundaryCoversTransitions D S) (hin : rayX w 1 ∈ S) :
    InteriorReaches D w :=
  interiorReaches_of_separated D w S hbd (separatedBy_of_covers D S hcov) hin






theorem chord_of_separated (D : BoxData) (w : Pt) (hw : w ∈ D.B) (S : Set Pt)
    (hbd : BoundedRight D S) (hsep : SeparatedBy D S) (hin : rayX w 1 ∈ S) :
    ∃ k : ℕ, 1 ≤ k ∧ rayX w k ∈ D.B ∧ (∀ j : ℕ, 1 ≤ j → j < k → rayX w j ∉ D.B) :=
  chord_of_interiorReaches D w hw (interiorReaches_of_separated D w S hbd hsep hin)






theorem chord_split_of_separated (D : BoxData) (w : Pt) (hw : w ∈ D.B) (S : Set Pt)
    (hbd : BoundedRight D S) (hsep : SeparatedBy D S) (hin : rayX w 1 ∈ S)
    (arc : List Pt) (harcND : arc.Nodup) (harc : ∀ p ∈ arc, p ∈ D.B) :
    ∃ k : ℕ, 1 ≤ k ∧ rayX w k ∈ D.B ∧ (arc ++ chordInterior w k).Nodup :=
  chord_split_of_core D w hw (interiorReaches_of_separated D w S hbd hsep hin) arc harcND harc

end StatMech.Onsager.InteriorReaches
