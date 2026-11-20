/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Mathlib
import Code.Sharpness.MultiReplica
import Code.Sharpness.FluxEdgeCopyBridge
import Code.Walls.gc85bthreereplicaswitch
import Code.Walls.gc86brerouteinjection
import Code.Walls.gc87brerouteinjection
import Code.Walls.vbgtriangle

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {W : Type*} [DecidableEq W] [Fintype W]

















theorem ghg_oddComp_eq (ends : ι → Sym2 W) (R : Finset ι)
    (hnd : ∀ i ∈ R, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends R = ({o, x, y, g} : Finset W))
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) :
    (compOf ends R o).filter (fun v => Odd (degK ends R v))
      = insert o ((({x, y, g} : Finset W)).filter (fun w => connK ends R o w)) := by
  ext v
  simp only [Finset.mem_filter, RandomCurrent.mem_compOf, Finset.mem_insert]
  constructor
  · rintro ⟨hconn, hodd⟩
    
    have hv : v ∈ ({o, x, y, g} : Finset W) := by rw [← hsrc, RandomCurrent.mem_sources]; exact hodd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · refine Or.inr ?_
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨by tauto, hconn⟩
    · refine Or.inr ?_
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨by tauto, hconn⟩
    · refine Or.inr ?_
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨by tauto, hconn⟩
  · rintro (rfl | hv)
    · 
      refine ⟨Relation.ReflTransGen.refl, ?_⟩
      rw [← RandomCurrent.mem_sources, hsrc]; simp
    · simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hv
      obtain ⟨hw, hconn⟩ := hv
      refine ⟨hconn, ?_⟩
      rw [← RandomCurrent.mem_sources, hsrc]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto





theorem ghg_conn_count_odd (ends : ι → Sym2 W) (R : Finset ι)
    (hnd : ∀ i ∈ R, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends R = ({o, x, y, g} : Finset W))
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) :
    Odd (#((({x, y, g} : Finset W)).filter (fun w => connK ends R o w))) := by
  
  have hsum_even := sum_deg_comp_even ends R hnd o
  have hcount_even : Even (#((compOf ends R o).filter (fun v => Odd (degK ends R v)))) :=
    (RandomCurrent.even_sum_iff_even_count _ _).1 hsum_even
  
  rw [ghg_oddComp_eq ends R hnd hsrc hox hoy hog] at hcount_even
  
  have honotin : o ∉ (({x, y, g} : Finset W)).filter (fun w => connK ends R o w) := by
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    rintro ⟨h, _⟩
    rcases h with rfl | rfl | rfl
    · exact hox rfl
    · exact hoy rfl
    · exact hog rfl
  rw [Finset.card_insert_of_notMem honotin] at hcount_even
  
  rcases hcount_even with ⟨t, ht⟩
  exact ⟨t - 1, by omega⟩



theorem ghg_flux_dichotomy (ends : ι → Sym2 W) (R : Finset ι)
    (hnd : ∀ i ∈ R, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends R = ({o, x, y, g} : Finset W))
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) :
    Odd (#((({x, y, g} : Finset W)).filter (fun w => connK ends R o w))) :=
  ghg_conn_count_odd ends R hnd hsrc hox hoy hog





theorem ghg_one_or_three (ends : ι → Sym2 W) (R : Finset ι)
    (hnd : ∀ i ∈ R, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends R = ({o, x, y, g} : Finset W))
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g) :
    #((({x, y, g} : Finset W)).filter (fun w => connK ends R o w)) = 1
      ∨ #((({x, y, g} : Finset W)).filter (fun w => connK ends R o w)) = 3 := by
  have hodd := ghg_conn_count_odd ends R hnd hsrc hox hoy hog
  
  have hle : #((({x, y, g} : Finset W)).filter (fun w => connK ends R o w)) ≤ 3 := by
    calc _ ≤ #({x, y, g} : Finset W) := Finset.card_filter_le _ _
      _ ≤ 3 := by
        refine le_trans (Finset.card_insert_le _ _) ?_
        refine le_trans (Nat.add_le_add_right (Finset.card_insert_le _ _) 1) ?_
        simp
  rcases hodd with ⟨t, ht⟩
  omega




theorem ghg_all_three_of_not_one (ends : ι → Sym2 W) (R : Finset ι)
    (hnd : ∀ i ∈ R, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends R = ({o, x, y, g} : Finset W))
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hne1 : #((({x, y, g} : Finset W)).filter (fun w => connK ends R o w)) ≠ 1) :
    connK ends R o x ∧ connK ends R o y ∧ connK ends R o g := by
  have h3 : #((({x, y, g} : Finset W)).filter (fun w => connK ends R o w)) = 3 :=
    (ghg_one_or_three ends R hnd hsrc hox hoy hog hxy hxg hyg).resolve_left hne1
  
  have hcard3 : #({x, y, g} : Finset W) = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxg]),
        Finset.card_insert_of_notMem (by simp [hyg]), Finset.card_singleton]
  have heq : (({x, y, g} : Finset W)).filter (fun w => connK ends R o w) = {x, y, g} :=
    Finset.filter_true_of_mem (fun w hw => by
      by_contra hcon
      have hsub : (({x, y, g} : Finset W)).filter (fun w => connK ends R o w) ⊂ {x, y, g} := by
        refine Finset.ssubset_iff_of_subset (Finset.filter_subset _ _) |>.2 ⟨w, hw, ?_⟩
        simp only [Finset.mem_filter]; tauto
      have := Finset.card_lt_card hsub
      omega)
  refine ⟨?_, ?_, ?_⟩
  · have hmem : x ∈ (({x, y, g} : Finset W)).filter (fun w => connK ends R o w) := by
      rw [heq]; simp
    exact (Finset.mem_filter.1 hmem).2
  · have hmem : y ∈ (({x, y, g} : Finset W)).filter (fun w => connK ends R o w) := by
      rw [heq]; simp
    exact (Finset.mem_filter.1 hmem).2
  · have hmem : g ∈ (({x, y, g} : Finset W)).filter (fun w => connK ends R o w) := by
      rw [heq]; simp
    exact (Finset.mem_filter.1 hmem).2













theorem ghg_lemma2_is_switching (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset W) (hm : sources ends m = A)
    {u v : W} (huv : u ≠ v) :
    #(m.powerset.filter (fun K => sources ends K = A ∆ {u, v}))
      = (if connK ends m u v then #(m.powerset.filter (fun K => sources ends K = A)) else 0) :=
  RandomCurrent.switching_card ends m hnd A hm huv












theorem ghg_lemma1_is_vbg {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (β h : ℝ) (hβ : 0 ≤ β) (i j k : V) :
    StatMech.Ising.cov2 G β h i j * StatMech.Ising.cov2 G β h j k
      ≤ StatMech.Walls.VBG.vbg_var (StatMech.Ising.isingProb G β h) (fun s => StatMech.Ising.spin s j)
        * StatMech.Ising.cov2 G β h i k :=
  StatMech.Walls.VBG.vbg_cor1 G β h hβ i j k















theorem ghg_eq21_maps_to_bijection (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) :
    (gc85b_threeGapCount ends m o x y g ≤ 0 ↔ gc85b_ThreeCurrentBijection ends m o x y g)
      ∧ (gc87b_CogxgLeT3 ends m o x y g → gc85b_ThreeCurrentBijection ends m o x y g) :=
  ⟨gc85b_threeGapCount_nonpos_iff_bijection ends m o x y g,
   fun hle => gc87b_bijection_of_cogxg_le_T3 ends m hnd hsrc hox hoy hog hle⟩






theorem ghg_tri_nonvacuous :
    gc85b_pcount gc87b_triEnds (univ : Finset (Fin 3)) {0, 3} {1, 3} = 1
      ∧ gc87b_CogxgLeT3 gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3 :=
  gc87b_tri_residue_nonvacuous




































theorem ghg_graham_status : True := trivial

end StatMech.Walls
