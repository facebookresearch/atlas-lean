/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































































import Mathlib
import Code.Sharpness.Switching
import Code.Sharpness.SwitchingDichotomy
import Code.Sharpness.FluxEdgeCopyBridge
import Code.Walls.gc7core
import Code.Walls.gc8crossingallconn

open Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.show false
set_option linter.style.longLine false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent
open StatMech.Sharpness.FluxEdgeCopy

variable {ι V : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq V] [Fintype V]











def gc10_allConn (ends : ι → Sym2 V) (o x y g : V) (m : Finset ι) : Prop :=
  connK ends m o x ∧ connK ends m o y ∧ connK ends m o g





theorem gc10_allConn_pairwise (ends : ι → Sym2 V) (o x y g : V) (m : Finset ι)
    (h : gc10_allConn ends o x y g m) :
    connK ends m o x ∧ connK ends m o y ∧ connK ends m o g
      ∧ connK ends m x y ∧ connK ends m x g ∧ connK ends m y g := by
  obtain ⟨hox, hoy, hog⟩ := h
  refine ⟨hox, hoy, hog, ?_, ?_, ?_⟩
  · exact (connK_symm ends m hox).trans hoy
  · exact (connK_symm ends m hox).trans hog
  · exact (connK_symm ends m hoy).trans hog

















theorem gc10_allConnForcing_disconnect (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (o x y g : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hsrc : sources ends m = {o, x, y, g})
    (hog_disc : ¬ connK ends m o g) :
    ((connK ends m o x ∧ connK ends m y g) ∨ (connK ends m o y ∧ connK ends m x g))
      ∧ ¬ ((connK ends m o x ∧ connK ends m y g) ∧ (connK ends m o y ∧ connK ends m x g)) :=
  gc7_core_pathCrossing_dichotomy ends m hnd o x y g hox hoy hog hxy hxg hyg hsrc hog_disc

























theorem gc10_disconnect_iff_crossPairing (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (o x y g : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hsrc : sources ends m = {o, x, y, g}) :
    (¬ connK ends m o g)
      ↔ (gc8_caseA ends o x y g m ∨ gc8_caseB ends o x y g m) :=
  
  
  gc8_disconn_eq_union ends m hnd o x y g hox hoy hog hxy hxg hyg hsrc






theorem gc10_crossPairing_disjoint (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (o x y g : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hsrc : sources ends m = {o, x, y, g}) :
    ¬ (gc8_caseA ends o x y g m ∧ gc8_caseB ends o x y g m) :=
  gc8_caseA_caseB_disjoint ends m hnd o x y g hox hoy hog hxy hxg hyg hsrc













theorem gc10_allConn_of_no_crossPairing (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (o x y g : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hsrc : sources ends m = {o, x, y, g})
    (hnA : ¬ gc8_caseA ends o x y g m) (hnB : ¬ gc8_caseB ends o x y g m) :
    connK ends m o g := by
  by_contra hog_disc
  rcases (gc10_disconnect_iff_crossPairing ends m hnd o x y g
    hox hoy hog hxy hxg hyg hsrc).mp hog_disc with hA | hB
  · exact hnA hA
  · exact hnB hB






theorem gc10_allConnected_forced (ends : ι → Sym2 V) (o x y g : V) (m : Finset ι)
    (hox : connK ends m o x) (hoy : connK ends m o y) (hog : connK ends m o g) :
    gc10_allConn ends o x y g m :=
  ⟨hox, hoy, hog⟩













theorem gc10_allConnForcing (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (o x y g : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hsrc : sources ends m = {o, x, y, g})
    (harcx : connK ends m o x) (harcy : connK ends m o y) :
    
    ((connK ends m o g ∧ gc10_allConn ends o x y g m)
        ∨ gc8_caseA ends o x y g m ∨ gc8_caseB ends o x y g m)
    
    ∧ (connK ends m o g → ¬ gc8_caseA ends o x y g m)
    ∧ (connK ends m o g → ¬ gc8_caseB ends o x y g m)
    
    ∧ ¬ (gc8_caseA ends o x y g m ∧ gc8_caseB ends o x y g m) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · 
    by_cases hog_conn : connK ends m o g
    · exact Or.inl ⟨hog_conn, harcx, harcy, hog_conn⟩
    · exact Or.inr ((gc10_disconnect_iff_crossPairing ends m hnd o x y g
        hox hoy hog hxy hxg hyg hsrc).mp hog_conn)
  · 
    rintro hog_conn ⟨hdisc, _⟩; exact hdisc hog_conn
  · 
    rintro hog_conn ⟨hdisc, _⟩; exact hdisc hog_conn
  · 
    exact gc10_crossPairing_disjoint ends m hnd o x y g hox hoy hog hxy hxg hyg hsrc












theorem gc10_crossing_forces_allConn (ends : ι → Sym2 V) {o x y g w : V} (m : Finset ι)
    (hox : connK ends m o x) (hyg : connK ends m y g)
    (hwo : connK ends m w o) (hwy : connK ends m w y) :
    gc10_allConn ends o x y g m := by
  obtain ⟨hox', hoy', hog'⟩ :=
    gc7_core_crossing_forces_oneCluster ends m hox hyg hwo hwy
  exact ⟨hox', hoy', hog'⟩













theorem gc10_crossPairing_not_implies_disconnect :
    ∃ (ends : Fin 3 → Sym2 (Fin 4)) (m : Finset (Fin 3)),
      (connK ends m 0 1 ∧ connK ends m 2 3) ∧ connK ends m 0 3 := by
  
  refine ⟨fun i => if i = 0 then s(0, 1) else if i = 1 then s(1, 2) else s(2, 3),
    (univ : Finset (Fin 3)), ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · 
      refine Relation.ReflTransGen.single ⟨0, Finset.mem_univ _, ?_, ?_, ?_⟩ <;> decide
    · 
      refine Relation.ReflTransGen.single ⟨2, Finset.mem_univ _, ?_, ?_, ?_⟩ <;> decide
  · 
    refine Relation.ReflTransGen.head (b := (1 : Fin 4))
      ⟨0, Finset.mem_univ _, ?_, ?_, ?_⟩ ?_
    · decide
    · decide
    · decide
    refine Relation.ReflTransGen.head (b := (2 : Fin 4))
      ⟨1, Finset.mem_univ _, ?_, ?_, ?_⟩ ?_
    · decide
    · decide
    · decide
    refine Relation.ReflTransGen.single ⟨2, Finset.mem_univ _, ?_, ?_, ?_⟩ <;> decide
















theorem gc10_allConnForcing_trichotomy (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (o x y g : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hsrc : sources ends m = {o, x, y, g}) :
    (connK ends m o g)
      ∨ (connK ends m o x ∧ connK ends m y g)
      ∨ (connK ends m o y ∧ connK ends m x g) :=
  gc7_core_pathCrossing_trichotomy ends m hnd o x y g hox hoy hog hxy hxg hyg hsrc







variable {W : Type*} [Fintype W] [DecidableEq W]





theorem gc10_allConnForcing_disconnect_edgeCopy (G : SimpleGraph W) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ) (K : Finset (Copy G m)) (o x y g : W)
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hsrc : sources (endsM G m) K = ({o, x, y, g} : Finset W))
    (hog_disc : ¬ connK (endsM G m) K o g) :
    ((connK (endsM G m) K o x ∧ connK (endsM G m) K y g)
        ∨ (connK (endsM G m) K o y ∧ connK (endsM G m) K x g))
      ∧ ¬ ((connK (endsM G m) K o x ∧ connK (endsM G m) K y g)
        ∧ (connK (endsM G m) K o y ∧ connK (endsM G m) K x g)) :=
  gc10_allConnForcing_disconnect (endsM G m) K (fun i _ => endsM_not_isDiag G m i)
    o x y g hox hoy hog hxy hxg hyg hsrc hog_disc




theorem gc10_allConnForcing_trichotomy_edgeCopy (G : SimpleGraph W) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ) (K : Finset (Copy G m)) (o x y g : W)
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hsrc : sources (endsM G m) K = ({o, x, y, g} : Finset W)) :
    (connK (endsM G m) K o g)
      ∨ (connK (endsM G m) K o x ∧ connK (endsM G m) K y g)
      ∨ (connK (endsM G m) K o y ∧ connK (endsM G m) K x g) :=
  gc10_allConnForcing_trichotomy (endsM G m) K (fun i _ => endsM_not_isDiag G m i)
    o x y g hox hoy hog hxy hxg hyg hsrc




theorem gc10_allConnected_forced_edgeCopy (G : SimpleGraph W) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ) (K : Finset (Copy G m)) (o x y g : W)
    (hox : connK (endsM G m) K o x) (hoy : connK (endsM G m) K o y)
    (hog : connK (endsM G m) K o g) :
    gc10_allConn (endsM G m) o x y g K :=
  gc10_allConnected_forced (endsM G m) o x y g K hox hoy hog












theorem gc10_allConnForcing_nonvacuous :
    let ends : Fin 2 → Sym2 (Fin 4) := fun i => if i = 0 then s(0, 1) else s(2, 3)
    sources ends (univ : Finset (Fin 2)) = ({0, 1, 2, 3} : Finset (Fin 4))
      ∧ ¬ connK ends (univ : Finset (Fin 2)) 0 3
      ∧ connK ends (univ : Finset (Fin 2)) 0 1
      ∧ connK ends (univ : Finset (Fin 2)) 2 3 := by
  intro ends
  refine ⟨?_, ?_, ?_, ?_⟩
  · 
    decide
  · 
    intro hconn
    
    
    have hsep : ∀ a b : Fin 4, connK ends (univ : Finset (Fin 2)) a b →
        ((a = 0 ∨ a = 1) ↔ (b = 0 ∨ b = 1)) := by
      intro a b h
      induction h with
      | refl => rfl
      | tail _ hstep ih =>
        rename_i c d _
        obtain ⟨i, _, hc, hd, hne⟩ := hstep
        have hstep_sep : ((c = 0 ∨ c = 1) ↔ (d = 0 ∨ d = 1)) := by
          
          
          have hi : i = 0 ∨ i = 1 := by omega
          rcases hi with rfl | rfl
          · 
            have hc0 : c ∈ (s(0, 1) : Sym2 (Fin 4)) := by simpa only [ends, if_pos rfl] using hc
            have hd0 : d ∈ (s(0, 1) : Sym2 (Fin 4)) := by simpa only [ends, if_pos rfl] using hd
            rw [Sym2.mem_iff] at hc0 hd0
            constructor <;> (intro _; tauto)
          · 
            have hne1 : (1 : Fin 2) ≠ 0 := by decide
            have hc1 : c ∈ (s(2, 3) : Sym2 (Fin 4)) := by
              simpa only [ends, if_neg hne1] using hc
            have hd1 : d ∈ (s(2, 3) : Sym2 (Fin 4)) := by
              simpa only [ends, if_neg hne1] using hd
            rw [Sym2.mem_iff] at hc1 hd1
            
            constructor
            · intro h01; rcases h01 with h | h <;> rcases hc1 with h' | h' <;> omega
            · intro h01; rcases h01 with h | h <;> rcases hd1 with h' | h' <;> omega
        exact ih.trans hstep_sep
    have := (hsep 0 3 hconn).mp (Or.inl rfl)
    revert this; decide
  · 
    refine Relation.ReflTransGen.single ⟨0, Finset.mem_univ _, ?_, ?_, ?_⟩
    · change (0 : Fin 4) ∈ (s(0, 1) : Sym2 (Fin 4)); decide
    · change (1 : Fin 4) ∈ (s(0, 1) : Sym2 (Fin 4)); decide
    · decide
  · 
    refine Relation.ReflTransGen.single ⟨1, Finset.mem_univ _, ?_, ?_, ?_⟩
    · change (2 : Fin 4) ∈ (s(2, 3) : Sym2 (Fin 4)); decide
    · change (3 : Fin 4) ∈ (s(2, 3) : Sym2 (Fin 4)); decide
    · decide

end StatMech.Walls
