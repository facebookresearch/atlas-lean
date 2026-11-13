/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































import Mathlib
import Code.Walls.gc44flow

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
set_option linter.style.multiGoal false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK degK adjStep compOf switching_card
  exists_conn_set sources_symmDiff path_exists mem_sources)

section Abstract

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]





noncomputable def gc45_evenSub (ends : ι → Sym2 W) (M : Finset ι) : Finset (Finset ι) :=
  M.powerset.filter (fun S => sources ends S = (∅ : Finset W))


theorem gc45_E_eq_card_evenSub (ends : ι → Sym2 W) (M : Finset ι) :
    gc40_E ends M = #(gc45_evenSub ends M) := rfl


theorem gc45_empty_mem_evenSub (ends : ι → Sym2 W) (M : Finset ι) :
    (∅ : Finset ι) ∈ gc45_evenSub ends M := by
  rw [gc45_evenSub, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨Finset.empty_subset _, ?_⟩
  
  ext z
  simp only [mem_sources, Finset.notMem_empty, iff_false]
  intro hodd
  rw [degK] at hodd
  simp only [Finset.filter_empty, Finset.card_empty] at hodd
  exact (Nat.not_odd_zero hodd)




theorem gc45_evenSub_symmDiff_mem (ends : ι → Sym2 W) (M : Finset ι)
    {S T : Finset ι} (hS : S ∈ gc45_evenSub ends M) (hT : T ∈ gc45_evenSub ends M) :
    S ∆ T ∈ gc45_evenSub ends M := by
  rw [gc45_evenSub, Finset.mem_filter, Finset.mem_powerset] at hS hT ⊢
  refine ⟨?_, ?_⟩
  · 
    intro i hi
    rw [Finset.mem_symmDiff] at hi
    rcases hi with ⟨hiS, _⟩ | ⟨hiT, _⟩
    · exact hS.1 hiS
    · exact hT.1 hiT
  · 
    rw [sources_symmDiff, hS.2, hT.2, symmDiff_self]; rfl



theorem gc45_E_eq_one_of_evenSub_singleton (ends : ι → Sym2 W) (M : Finset ι)
    (h : gc45_evenSub ends M = {(∅ : Finset ι)}) :
    gc40_E ends M = 1 := by
  rw [gc45_E_eq_card_evenSub, h, Finset.card_singleton]







theorem gc45_E_eq_two_of_nullity_one (ends : ι → Sym2 W) (M : Finset ι) {C : Finset ι}
    (hCne : C ≠ (∅ : Finset ι))
    (h : gc45_evenSub ends M = {(∅ : Finset ι), C}) :
    gc40_E ends M = 2 := by
  rw [gc45_E_eq_card_evenSub, h]
  rw [Finset.card_pair (by exact fun heq => hCne heq.symm)]













theorem gc45_fibreDomReloc_of_injOn_subset (ends : ι → Sym2 W) (o x y g : W)
    (φ : Finset ι → Finset ι)
    (hmaps : ∀ M ∈ gc43_Lset ends o x y g, φ M ∈ gc43_Rset ends o x y g)
    (hsub : ∀ M ∈ gc43_Lset ends o x y g, M ⊆ φ M)
    (hinj : Set.InjOn φ (gc43_Lset ends o x y g)) :
    gc43_FibreDomReloc ends o x y g := by
  refine ⟨φ, hmaps, ?_⟩
  intro M' hM'
  set fib := (gc43_Lset ends o x y g).filter (fun M => φ M = M') with hfib
  
  have hcard : #fib ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [hfib, Finset.mem_filter] at ha hb
    exact hinj ha.1 hb.1 (ha.2.trans hb.2.symm)
  obtain ⟨M, hMsub⟩ := Finset.card_le_one_iff_subset_singleton.mp hcard
  by_cases hMmem : M ∈ fib
  · 
    have hfibeq : fib = {M} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hMmem, fun z hz => by
      have := hMsub hz; rwa [Finset.mem_singleton] at this⟩
    rw [hfibeq, Finset.sum_singleton]
    have hML : M ∈ gc43_Lset ends o x y g := by
      rw [hfib, Finset.mem_filter] at hMmem; exact hMmem.1
    have hφM : φ M = M' := by
      rw [hfib, Finset.mem_filter] at hMmem; exact hMmem.2
    have hsubM' : M ⊆ M' := by rw [← hφM]; exact hsub M hML
    exact gc43_E_le_of_subset ends hsubM'
  · 
    have hfibempty : fib = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro z hz
      have := hMsub hz
      rw [Finset.mem_singleton] at this
      rw [this] at hz
      exact hMmem hz
    rw [hfibempty, Finset.sum_empty]
    exact Nat.zero_le _










theorem gc45_FibreDomReloc_of_disjointBridge (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hbridge : gc44_DisjointBridge ends o x y g) :
    gc43_FibreDomReloc ends o x y g := by
  obtain ⟨P, hPsrc, hPdisj⟩ := hbridge
  refine gc45_fibreDomReloc_of_injOn_subset ends o x y g (fun M => M ∆ P) ?_ ?_ ?_
  · 
    intro M hM
    have hMmem := hM
    rw [gc43_Lset, Finset.mem_filter, Finset.mem_powerset] at hMmem
    obtain ⟨_, hMsrc, hMgate⟩ := hMmem
    exact gc44_shift_in_Rset_of_disjoint ends hnd (hPdisj M hM) hox hoy hog hxy hxg hyg
      hMsrc hPsrc hMgate
  · 
    intro M hM
    have hdisj : Disjoint M P := hPdisj M hM
    change M ⊆ M ∆ P
    rw [Disjoint.symmDiff_eq_sup hdisj]
    exact Finset.subset_union_left
  · 
    exact gc44_shift_injOn ends P (gc43_Lset ends o x y g)







def gc45_TreeLHS (ends : ι → Sym2 W) (o x y g : W) : Prop :=
  ∀ M ∈ gc43_Lset ends o x y g, gc40_E ends M = 1












theorem gc45_fibreDomReloc_of_count_le (ends : ι → Sym2 W) (o x y g : W)
    (htree : gc45_TreeLHS ends o x y g)
    (φ : Finset ι → Finset ι)
    (hmaps : ∀ M ∈ gc43_Lset ends o x y g, φ M ∈ gc43_Rset ends o x y g)
    (hcount : ∀ M' ∈ gc43_Rset ends o x y g,
        #((gc43_Lset ends o x y g).filter (fun M => φ M = M')) ≤ gc40_E ends M') :
    gc43_FibreDomReloc ends o x y g := by
  refine ⟨φ, hmaps, ?_⟩
  intro M' hM'
  set fib := (gc43_Lset ends o x y g).filter (fun M => φ M = M') with hfib
  
  have hsum : (∑ M ∈ fib, gc40_E ends M) = #fib := by
    rw [Finset.sum_congr rfl (fun M hM => ?_), Finset.sum_const, smul_eq_mul, mul_one]
    
    rw [hfib, Finset.mem_filter] at hM
    exact htree M hM.1
  rw [hsum]
  exact hcount M' hM'













def gc45_NullityOneRelocation (ends : ι → Sym2 W) (o x y g : W) : Prop :=
  ∃ φ : Finset ι → Finset ι,
    (∀ M ∈ gc43_Lset ends o x y g, φ M ∈ gc43_Rset ends o x y g)
      ∧ (∀ M' ∈ gc43_Rset ends o x y g,
          #((gc43_Lset ends o x y g).filter (fun M => φ M = M')) ≤ gc40_E ends M')




theorem gc45_FibreDomReloc_of_nullityOneReloc (ends : ι → Sym2 W) (o x y g : W)
    (htree : gc45_TreeLHS ends o x y g)
    (hreloc : gc45_NullityOneRelocation ends o x y g) :
    gc43_FibreDomReloc ends o x y g := by
  obtain ⟨φ, hmaps, hcount⟩ := hreloc
  exact gc45_fibreDomReloc_of_count_le ends o x y g htree φ hmaps hcount




theorem gc45_EMassResidue_of_nullityOneReloc (ends : ι → Sym2 W) (o x y g : W)
    (htree : gc45_TreeLHS ends o x y g)
    (hreloc : gc45_NullityOneRelocation ends o x y g) :
    gc42_EMassResidue ends o x y g :=
  gc43_EMass_of_fibreDomReloc ends o x y g
    (gc45_FibreDomReloc_of_nullityOneReloc ends o x y g htree hreloc)



theorem gc45_countIneq_of_nullityOneReloc (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (htree : gc45_TreeLHS ends o x y g)
    (hreloc : gc45_NullityOneRelocation ends o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc43_countIneq_of_fibreDomReloc ends hnd hox hoy hog hxy hxg hyg huniv
    (gc45_FibreDomReloc_of_nullityOneReloc ends o x y g htree hreloc)

end Abstract





















noncomputable def gc45_diamondEnds : Fin 4 → Sym2 (Fin 4) := ![s(0, 3), s(1, 3), s(0, 2), s(0, 3)]


theorem gc45_diamondEnds_loopless : ∀ i : Fin 4, ¬ (gc45_diamondEnds i).IsDiag := by decide


theorem gc45_diamondEnds_univ_sources :
    sources gc45_diamondEnds (univ : Finset (Fin 4)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by decide



theorem gc45_diamond_evenSub_univ :
    gc45_evenSub gc45_diamondEnds (univ : Finset (Fin 4))
      = {(∅ : Finset (Fin 4)), ({0, 3} : Finset (Fin 4))} := by decide



theorem gc45_diamond_E_univ_eq_two :
    gc40_E gc45_diamondEnds (univ : Finset (Fin 4)) = 2 :=
  gc45_E_eq_two_of_nullity_one gc45_diamondEnds (univ : Finset (Fin 4))
    (by decide : ({0, 3} : Finset (Fin 4)) ≠ (∅ : Finset (Fin 4)))
    gc45_diamond_evenSub_univ




theorem gc45_diamond_not_forest : ¬ gc44_ForestHyp gc45_diamondEnds := by
  intro hforest
  have h := hforest (univ : Finset (Fin 4))
  rw [gc45_diamond_E_univ_eq_two] at h
  exact absurd h (by decide)




theorem gc45_diamond_Lset :
    gc43_Lset gc45_diamondEnds (0 : Fin 4) 1 2 3
      = {({0, 1} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4))} := by
  rw [gc43_Lset, ← Finset.filter_filter]
  rw [show ((univ : Finset (Fin 4)).powerset.filter
        (fun M => sources gc45_diamondEnds M = ({0, 1} : Finset (Fin 4))))
      = {({0, 1} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4))} from by decide]
  
  have h01 : connK gc45_diamondEnds ({0, 1} : Finset (Fin 4)) (1 : Fin 4) (3 : Fin 4) :=
    Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩
  have h13 : connK gc45_diamondEnds ({1, 3} : Finset (Fin 4)) (1 : Fin 4) (3 : Fin 4) :=
    Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩
  rw [Finset.filter_insert, Finset.filter_singleton, if_pos h01, if_pos h13]





theorem gc45_diamond_reach_12_subset {v : Fin 4}
    (h : connK gc45_diamondEnds ({1, 2} : Finset (Fin 4)) (0 : Fin 4) v) :
    v ∈ ({0, 2} : Finset (Fin 4)) := by
  induction h with
  | refl => decide
  | tail _ hstep ih =>
    obtain ⟨i, hi, ha, hb, hne⟩ := hstep
    
    
    
    fin_cases hi <;>
      simp only [gc45_diamondEnds, Matrix.cons_val_one, Matrix.cons_val_zero,
        Sym2.mem_iff, Matrix.cons_val] at ha hb ⊢ <;>
      rw [Finset.mem_insert, Finset.mem_singleton] at ih ⊢ <;>
      omega



theorem gc45_diamond_not_conn_12_01 :
    ¬ connK gc45_diamondEnds ({1, 2} : Finset (Fin 4)) (0 : Fin 4) (1 : Fin 4) := by
  intro h
  have := gc45_diamond_reach_12_subset h
  revert this; decide




theorem gc45_diamond_Rset :
    gc43_Rset gc45_diamondEnds (0 : Fin 4) 1 2 3 = {(univ : Finset (Fin 4))} := by
  rw [gc43_Rset, ← Finset.filter_filter]
  
  rw [show ((univ : Finset (Fin 4)).powerset.filter
        (fun M => sources gc45_diamondEnds M = ({0, 1, 2, 3} : Finset (Fin 4))))
      = {({1, 2} : Finset (Fin 4)), (univ : Finset (Fin 4))} from by decide]
  
  have hox : connK gc45_diamondEnds (univ : Finset (Fin 4)) (0 : Fin 4) (1 : Fin 4) :=
    Relation.ReflTransGen.head (b := (3 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩
      (Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩)
  have hoy : connK gc45_diamondEnds (univ : Finset (Fin 4)) (0 : Fin 4) (2 : Fin 4) :=
    Relation.ReflTransGen.single ⟨2, by decide, by decide, by decide, by decide⟩
  have hog : connK gc45_diamondEnds (univ : Finset (Fin 4)) (0 : Fin 4) (3 : Fin 4) :=
    Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩
  
  have hng : ¬ (connK gc45_diamondEnds ({1, 2} : Finset (Fin 4)) (0 : Fin 4) (1 : Fin 4)
      ∧ connK gc45_diamondEnds ({1, 2} : Finset (Fin 4)) (0 : Fin 4) (2 : Fin 4)
      ∧ connK gc45_diamondEnds ({1, 2} : Finset (Fin 4)) (0 : Fin 4) (3 : Fin 4)) := by
    rintro ⟨h01, _, _⟩
    exact gc45_diamond_not_conn_12_01 h01
  rw [Finset.filter_insert, if_neg hng, Finset.filter_singleton, if_pos ⟨hox, hoy, hog⟩]



theorem gc45_diamond_TreeLHS : gc45_TreeLHS gc45_diamondEnds (0 : Fin 4) 1 2 3 := by
  intro M hM
  rw [gc45_diamond_Lset, Finset.mem_insert, Finset.mem_singleton] at hM
  rcases hM with h | h <;> subst h <;> decide






theorem gc45_diamond_NullityOneRelocation :
    gc45_NullityOneRelocation gc45_diamondEnds (0 : Fin 4) 1 2 3 := by
  refine ⟨fun _ => (univ : Finset (Fin 4)), ?_, ?_⟩
  · intro M hM
    rw [gc45_diamond_Rset, Finset.mem_singleton]
  · intro M' hM'
    rw [gc45_diamond_Rset, Finset.mem_singleton] at hM'
    subst hM'
    rw [gc45_diamond_Lset]
    
    rw [show ({({0, 1} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4))} : Finset (Finset (Fin 4))).filter
          (fun M => (univ : Finset (Fin 4)) = (univ : Finset (Fin 4)))
        = {({0, 1} : Finset (Fin 4)), ({1, 3} : Finset (Fin 4))} from by decide]
    rw [gc45_diamond_E_univ_eq_two]
    decide






theorem gc45_diamond_core : gc39_ThreeColouringCountIneq gc45_diamondEnds (0 : Fin 4) 1 2 3 :=
  gc45_countIneq_of_nullityOneReloc gc45_diamondEnds gc45_diamondEnds_loopless
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    gc45_diamondEnds_univ_sources gc45_diamond_TreeLHS gc45_diamond_NullityOneRelocation




theorem gc45_diamond_EMassResidue : gc42_EMassResidue gc45_diamondEnds (0 : Fin 4) 1 2 3 :=
  gc45_EMassResidue_of_nullityOneReloc gc45_diamondEnds (0 : Fin 4) 1 2 3
    gc45_diamond_TreeLHS gc45_diamond_NullityOneRelocation





theorem gc45_reloc_applies_diamond :
    (∀ i : Fin 4, ¬ (gc45_diamondEnds i).IsDiag)
      ∧ sources gc45_diamondEnds (univ : Finset (Fin 4)) = ({0, 1, 2, 3} : Finset (Fin 4))
      ∧ gc40_E gc45_diamondEnds (univ : Finset (Fin 4)) = 2
      ∧ gc45_TreeLHS gc45_diamondEnds (0 : Fin 4) 1 2 3
      ∧ gc45_NullityOneRelocation gc45_diamondEnds (0 : Fin 4) 1 2 3 :=
  ⟨gc45_diamondEnds_loopless, gc45_diamondEnds_univ_sources, gc45_diamond_E_univ_eq_two,
    gc45_diamond_TreeLHS, gc45_diamond_NullityOneRelocation⟩

end StatMech.Walls
