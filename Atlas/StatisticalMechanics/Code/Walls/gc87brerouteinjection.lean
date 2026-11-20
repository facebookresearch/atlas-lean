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
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {W : Type*} [DecidableEq W] [Fintype W]













noncomputable def gc87b_T3 (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) : ℕ :=
  ∑ J₁ ∈ (m.powerset.filter (fun K => sources ends K = ∅)).filter
      (fun J₁ => connK ends (m \ J₁) o x ∧ connK ends (m \ J₁) o y ∧ connK ends (m \ J₁) o g),
    gc86b_ncount ends (m \ J₁) ∅



def gc87b_slack (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) : ℤ :=
  ((gc85b_pcount ends m ∅ {o, g} : ℤ) + (gc85b_pcount ends m ∅ {o, x} : ℤ)
      + (gc85b_pcount ends m ∅ {o, y} : ℤ)) - (gc85b_pcount ends m ∅ ∅ : ℤ)










theorem gc87b_connK_mono (ends : ι → Sym2 W) {K R : Finset ι} (hKR : K ⊆ R) {a b : W}
    (h : connK ends K a b) : connK ends R a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      obtain ⟨i, hi, ha, hb, hne⟩ := hstep
      exact ih.tail ⟨i, hKR hi, ha, hb, hne⟩




theorem gc87b_ncount_xg_eq (ends : ι → Sym2 W) (R : Finset ι)
    (hnd : ∀ i ∈ R, ¬ (ends i).IsDiag) {x g : W} (hxg : x ≠ g) :
    gc86b_ncount ends R {x, g}
      = if connK ends R x g then gc86b_ncount ends R ∅ else 0 := by
  by_cases hconn : connK ends R x g
  · rw [if_pos hconn, gc86b_ncount_conn_eq ends R hxg hconn]
  · rw [if_neg hconn]
    
    unfold gc86b_ncount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro K hK
    rw [Finset.mem_powerset] at hK
    intro hKsrc
    
    have hKnd : ∀ i ∈ K, ¬ (ends i).IsDiag := fun i hi => hnd i (hK hi)
    have hx_odd : Odd (degK ends K x) := by
      rw [← RandomCurrent.mem_sources, hKsrc]; simp
    have hbdry : ∀ w, Odd (degK ends K w) → w = x ∨ w = g := by
      intro w hw
      have : w ∈ sources ends K := by rw [RandomCurrent.mem_sources]; exact hw
      rw [hKsrc] at this
      simpa only [Finset.mem_insert, Finset.mem_singleton] using this
    have hconnK : connK ends K x g := RandomCurrent.path_exists ends K hKnd x g hx_odd hbdry hxg
    
    exact hconn (gc87b_connK_mono ends hK hconnK)










theorem gc87b_cogxg_fiber_conn (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W} (hxg : x ≠ g) :
    gc85b_pcount ends m {o, g} {x, g}
      = ∑ K₁ ∈ (m.powerset.filter (fun K => sources ends K = {o, g})).filter
          (fun K₁ => connK ends (m \ K₁) x g),
        gc86b_ncount ends (m \ K₁) ∅ := by
  rw [gc85b_pcount_fiber ends m {o, g} {x, g}]
  
  rw [Finset.sum_congr rfl (fun K₁ hK₁ => by
        simp only [Finset.mem_filter, Finset.mem_powerset] at hK₁
        have hRnd : ∀ i ∈ m \ K₁, ¬ (ends i).IsDiag := fun i hi => hnd i (Finset.mem_sdiff.1 hi).1
        exact gc87b_ncount_xg_eq ends (m \ K₁) hRnd hxg)]
  
  rw [← Finset.sum_filter, Finset.filter_filter]












theorem gc87b_fiber_slack_eq_of_allConn (ends : ι → Sym2 W) (R : Finset ι) {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hcx : connK ends R o x) (hcy : connK ends R o y) (hcg : connK ends R o g) :
    (gc86b_ncount ends R {o, g} : ℤ) + (gc86b_ncount ends R {o, x} : ℤ)
        + (gc86b_ncount ends R {o, y} : ℤ) - (gc86b_ncount ends R ∅ : ℤ)
      = 2 * (gc86b_ncount ends R ∅ : ℤ) := by
  have hg := gc86b_ncount_conn_eq ends R hog hcg
  have hx := gc86b_ncount_conn_eq ends R hox hcx
  have hy := gc86b_ncount_conn_eq ends R hoy hcy
  rw [hg, hx, hy]; ring








theorem gc87b_slack_fiber (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    gc87b_slack ends m o x y g
      = ∑ K₁ ∈ m.powerset.filter (fun K => sources ends K = ∅),
          ((gc86b_ncount ends (m \ K₁) {o, g} : ℤ) + (gc86b_ncount ends (m \ K₁) {o, x} : ℤ)
            + (gc86b_ncount ends (m \ K₁) {o, y} : ℤ) - (gc86b_ncount ends (m \ K₁) ∅ : ℤ)) := by
  unfold gc87b_slack
  rw [gc85b_pcount_fiber ends m ∅ {o, g}, gc85b_pcount_fiber ends m ∅ {o, x},
      gc85b_pcount_fiber ends m ∅ {o, y}, gc85b_pcount_fiber ends m ∅ ∅]
  push_cast
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]




theorem gc87b_T3_eq_sum_if (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    (gc87b_T3 ends m o x y g : ℤ)
      = ∑ K₁ ∈ m.powerset.filter (fun K => sources ends K = ∅),
          (if connK ends (m \ K₁) o x ∧ connK ends (m \ K₁) o y ∧ connK ends (m \ K₁) o g
            then (gc86b_ncount ends (m \ K₁) ∅ : ℤ) else 0) := by
  unfold gc87b_T3
  push_cast
  rw [Finset.sum_filter]












theorem gc87b_two_T3_le_slack (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) :
    2 * (gc87b_T3 ends m o x y g : ℤ) ≤ gc87b_slack ends m o x y g := by
  rw [gc87b_slack_fiber ends m o x y g]
  rw [show (2 * (gc87b_T3 ends m o x y g : ℤ))
        = ∑ K₁ ∈ m.powerset.filter (fun K => sources ends K = ∅),
            (if connK ends (m \ K₁) o x ∧ connK ends (m \ K₁) o y ∧ connK ends (m \ K₁) o g
              then 2 * (gc86b_ncount ends (m \ K₁) ∅ : ℤ) else 0) from ?_]
  · 
    refine Finset.sum_le_sum (fun K₁ hK₁ => ?_)
    simp only [Finset.mem_filter, Finset.mem_powerset] at hK₁
    obtain ⟨hK₁m, hK₁src⟩ := hK₁
    
    have hRsrc : sources ends (m \ K₁) = ({o, x, y, g} : Finset W) := by
      rw [gc86b_sources_sdiff_of_empty ends hK₁m hK₁src, hsrc]
    have hRnd : ∀ i ∈ m \ K₁, ¬ (ends i).IsDiag := fun i hi => hnd i (Finset.mem_sdiff.1 hi).1
    
    have hnn : 0 ≤ (gc86b_ncount ends (m \ K₁) {o, g} : ℤ) + (gc86b_ncount ends (m \ K₁) {o, x} : ℤ)
        + (gc86b_ncount ends (m \ K₁) {o, y} : ℤ) - (gc86b_ncount ends (m \ K₁) ∅ : ℤ) := by
      have := gc86b_strong_of_conn ends (m \ K₁) hRnd hRsrc hox hoy hog
      
      zify at this; linarith
    by_cases hconn : connK ends (m \ K₁) o x ∧ connK ends (m \ K₁) o y ∧ connK ends (m \ K₁) o g
    · rw [if_pos hconn]
      obtain ⟨hcx, hcy, hcg⟩ := hconn
      rw [gc87b_fiber_slack_eq_of_allConn ends (m \ K₁) hox hoy hog hcx hcy hcg]
    · rw [if_neg hconn]; exact hnn
  · rw [gc87b_T3_eq_sum_if ends m o x y g, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun K₁ hK₁ => ?_)
    by_cases hconn : connK ends (m \ K₁) o x ∧ connK ends (m \ K₁) o y ∧ connK ends (m \ K₁) o g
    · rw [if_pos hconn, if_pos hconn]
    · rw [if_neg hconn, if_neg hconn, mul_zero]





















def gc87b_CogxgLeT3 (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) : Prop :=
  gc85b_pcount ends m {o, g} {x, g} ≤ gc87b_T3 ends m o x y g




theorem gc87b_residual_of_cogxg_le_T3 (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hle : gc87b_CogxgLeT3 ends m o x y g) :
    gc86b_CogxgResidual ends m o x y g := by
  unfold gc86b_CogxgResidual
  unfold gc87b_CogxgLeT3 at hle
  have h2 : 2 * (gc87b_T3 ends m o x y g : ℤ) ≤ gc87b_slack ends m o x y g :=
    gc87b_two_T3_le_slack ends m hnd hsrc hox hoy hog
  have hcog : (gc85b_pcount ends m {o, g} {x, g} : ℤ) ≤ (gc87b_T3 ends m o x y g : ℤ) := by
    exact_mod_cast hle
  
  have : gc87b_slack ends m o x y g
      = ((gc85b_pcount ends m ∅ {o, g} : ℤ) + (gc85b_pcount ends m ∅ {o, x} : ℤ)
          + (gc85b_pcount ends m ∅ {o, y} : ℤ)) - (gc85b_pcount ends m ∅ ∅ : ℤ) := rfl
  linarith





theorem gc87b_bijection_of_cogxg_le_T3 (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hle : gc87b_CogxgLeT3 ends m o x y g) :
    gc85b_ThreeCurrentBijection ends m o x y g :=
  gc86b_bijection_of_residual ends m o x y g
    (gc87b_residual_of_cogxg_le_T3 ends m hnd hsrc hox hoy hog hle)












def gc87b_triEnds : Fin 3 → Sym2 (Fin 4) :=
  fun i => if i = 0 then s(0, 3) else if i = 1 then s(1, 3) else s(2, 3)




theorem gc87b_tri_sources :
    sources gc87b_triEnds (univ : Finset (Fin 3)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
  decide


theorem gc87b_one_le_ncount_empty (ends : ι → Sym2 W) (R : Finset ι) :
    1 ≤ gc86b_ncount ends R ∅ := by
  unfold gc86b_ncount
  rw [Finset.one_le_card]
  refine ⟨∅, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset, true_and]
  ext v; simp [RandomCurrent.sources, degK]




theorem gc87b_one_le_T3_of_allConn (ends : ι → Sym2 W) (m : Finset ι) {o x y g : W}
    (hcx : connK ends m o x) (hcy : connK ends m o y) (hcg : connK ends m o g) :
    1 ≤ gc87b_T3 ends m o x y g := by
  unfold gc87b_T3
  have hmem : (∅ : Finset ι) ∈ (m.powerset.filter (fun K => sources ends K = ∅)).filter
      (fun J₁ => connK ends (m \ J₁) o x ∧ connK ends (m \ J₁) o y ∧ connK ends (m \ J₁) o g) := by
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset, true_and,
      Finset.sdiff_empty]
    refine ⟨?_, hcx, hcy, hcg⟩
    ext v; simp [RandomCurrent.sources, degK]
  calc (1 : ℕ) ≤ gc86b_ncount ends (m \ ∅) ∅ := by rw [Finset.sdiff_empty]; exact gc87b_one_le_ncount_empty ends m
    _ ≤ _ := Finset.single_le_sum (f := fun J₁ => gc86b_ncount ends (m \ J₁) ∅)
              (fun _ _ => Nat.zero_le _) hmem





theorem gc87b_tri_residue_nonvacuous :
    gc85b_pcount gc87b_triEnds (univ : Finset (Fin 3)) {0, 3} {1, 3} = 1
      ∧ gc87b_CogxgLeT3 gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3 := by
  have hcog : gc85b_pcount gc87b_triEnds (univ : Finset (Fin 3)) {0, 3} {1, 3} = 1 := by
    unfold gc85b_pcount; decide
  refine ⟨hcog, ?_⟩
  
  unfold gc87b_CogxgLeT3
  rw [hcog]
  refine gc87b_one_le_T3_of_allConn gc87b_triEnds (univ : Finset (Fin 3)) ?_ ?_ ?_
  
  · refine Relation.ReflTransGen.head (b := (3 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩
      (Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩)
  
  · refine Relation.ReflTransGen.head (b := (3 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩
      (Relation.ReflTransGen.single ⟨2, by decide, by decide, by decide, by decide⟩)
  
  · exact Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩





























theorem gc87b_local_template_insufficient :
    ∃ (nS nT : ℕ) (adj : Fin nS → Fin nT → Prop),
      
      nS ≤ nT
      
      ∧ ∃ (fixedChoice : Fin nS → Fin nT), ¬ Function.Injective fixedChoice := by
  
  
  refine ⟨2, 2, fun _ _ => True, le_refl 2, fun _ => 0, ?_⟩
  intro hinj
  have := hinj (a₁ := 0) (a₂ := 1) rfl
  simp at this
























theorem gc87b_cogxg_le_T3_status (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxg : x ≠ g) :
    
    (gc85b_pcount ends m {o, g} {x, g}
        = ∑ K₁ ∈ (m.powerset.filter (fun K => sources ends K = {o, g})).filter
            (fun K₁ => connK ends (m \ K₁) x g),
          gc86b_ncount ends (m \ K₁) ∅)
    
    ∧ (2 * (gc87b_T3 ends m o x y g : ℤ) ≤ gc87b_slack ends m o x y g)
    
    ∧ (gc87b_CogxgLeT3 ends m o x y g → gc85b_ThreeCurrentBijection ends m o x y g) :=
  ⟨gc87b_cogxg_fiber_conn (o := o) (x := x) (y := y) (g := g) ends m hnd hxg,
   gc87b_two_T3_le_slack ends m hnd hsrc hox hoy hog,
   fun hle => gc87b_bijection_of_cogxg_le_T3 ends m hnd hsrc hox hoy hog hle⟩

end StatMech.Walls
