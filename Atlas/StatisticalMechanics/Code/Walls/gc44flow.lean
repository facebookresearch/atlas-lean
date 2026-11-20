/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































import Mathlib
import Code.Walls.gc43graham

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







def gc44_ForestHyp (ends : ι → Sym2 W) : Prop :=
  ∀ M : Finset ι, gc40_E ends M = 1








theorem gc44_fibreDomReloc_of_injOn_of_E_one (ends : ι → Sym2 W) (o x y g : W)
    (hE : gc44_ForestHyp ends)
    (φ : Finset ι → Finset ι)
    (hmaps : ∀ M ∈ gc43_Lset ends o x y g, φ M ∈ gc43_Rset ends o x y g)
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
  
  have hsum : (∑ M ∈ fib, gc40_E ends M) = #fib := by
    rw [Finset.sum_congr rfl (fun M _ => hE M), Finset.sum_const, smul_eq_mul, mul_one]
  rw [hsum, hE M']
  exact hcard





theorem gc44_sd_ox_yg {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g) :
    ({o, x} : Finset W) ∆ ({y, g} : Finset W) = ({o, x, y, g} : Finset W) := by
  ext z; simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  by_cases h1 : z = o <;> by_cases h2 : z = x <;> by_cases h3 : z = y <;> by_cases h4 : z = g <;>
    subst_vars <;> simp_all




theorem gc44_shift_sources (ends : ι → Sym2 W) {M P : Finset ι} {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hM : sources ends M = ({o, x} : Finset W)) (hP : sources ends P = ({y, g} : Finset W)) :
    sources ends (M ∆ P) = ({o, x, y, g} : Finset W) := by
  rw [sources_symmDiff, hM, hP, gc44_sd_ox_yg hox hoy hog hxy hxg hyg]




theorem gc44_shift_injOn (ends : ι → Sym2 W) (P : Finset ι) (s : Finset (Finset ι)) :
    Set.InjOn (fun M => M ∆ P) s := by
  intro a ha b hb h
  simp only at h
  have : (a ∆ P) ∆ P = (b ∆ P) ∆ P := by rw [h]
  rwa [symmDiff_symmDiff_cancel_right, symmDiff_symmDiff_cancel_right] at this





theorem gc44_shift_in_Rset_of_disjoint (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {M P : Finset ι} (hdisj : Disjoint M P) {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hM : sources ends M = ({o, x} : Finset W)) (hP : sources ends P = ({y, g} : Finset W))
    (hxg_conn : connK ends M x g) :
    M ∆ P ∈ gc43_Rset ends o x y g := by
  
  have hun : M ∆ P = M ∪ P := Disjoint.symmDiff_eq_sup hdisj
  have hPsub : P ⊆ univ \ M := by
    intro i hi
    rw [Finset.mem_sdiff]
    exact ⟨Finset.mem_univ i, fun hiM => (Finset.disjoint_left.mp hdisj hiM) hi⟩
  obtain ⟨hsrc', hox', hoy', hog'⟩ :=
    gc43_reloc_in_RHS ends hnd hPsub hox hoy hog hxy hxg hyg hM hP hxg_conn
  rw [gc43_Rset, Finset.mem_filter, Finset.mem_powerset]
  rw [hun]
  exact ⟨Finset.subset_univ _, hsrc', hox', hoy', hog'⟩






def gc44_DisjointBridge (ends : ι → Sym2 W) (o x y g : W) : Prop :=
  ∃ P : Finset ι, sources ends P = ({y, g} : Finset W)
    ∧ ∀ M ∈ gc43_Lset ends o x y g, Disjoint M P











theorem gc44_FibreDomReloc_of_forest (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hforest : gc44_ForestHyp ends) (hbridge : gc44_DisjointBridge ends o x y g) :
    gc43_FibreDomReloc ends o x y g := by
  obtain ⟨P, hPsrc, hPdisj⟩ := hbridge
  refine gc44_fibreDomReloc_of_injOn_of_E_one ends o x y g hforest (fun M => M ∆ P) ?_ ?_
  · 
    intro M hM
    have hMmem := hM
    rw [gc43_Lset, Finset.mem_filter, Finset.mem_powerset] at hMmem
    obtain ⟨_, hMsrc, hMgate⟩ := hMmem
    exact gc44_shift_in_Rset_of_disjoint ends hnd (hPdisj M hM) hox hoy hog hxy hxg hyg
      hMsrc hPsrc hMgate
  · 
    exact gc44_shift_injOn ends P (gc43_Lset ends o x y g)




theorem gc44_countIneq_of_forest (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hforest : gc44_ForestHyp ends) (hbridge : gc44_DisjointBridge ends o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc43_countIneq_of_fibreDomReloc ends hnd hox hoy hog hxy hxg hyg huniv
    (gc44_FibreDomReloc_of_forest ends hnd hox hoy hog hxy hxg hyg hforest hbridge)



theorem gc44_EMassResidue_of_forest (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hforest : gc44_ForestHyp ends) (hbridge : gc44_DisjointBridge ends o x y g) :
    gc42_EMassResidue ends o x y g :=
  gc43_EMass_of_fibreDomReloc ends o x y g
    (gc44_FibreDomReloc_of_forest ends hnd hox hoy hog hxy hxg hyg hforest hbridge)

end Abstract












theorem gc44_claw_forest : gc44_ForestHyp gc40_clawEnds := by
  intro M
  revert M
  decide



theorem gc44_claw_bridge : gc44_DisjointBridge gc40_clawEnds (0 : Fin 4) 1 2 3 := by
  refine ⟨({2} : Finset (Fin 3)), by decide, ?_⟩
  intro M hM
  rw [gc43_claw_Lset, Finset.mem_singleton] at hM
  subst hM
  decide



theorem gc44_claw_FibreDomReloc : gc43_FibreDomReloc gc40_clawEnds (0 : Fin 4) 1 2 3 :=
  gc44_FibreDomReloc_of_forest gc40_clawEnds gc40_clawEnds_loopless
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    gc44_claw_forest gc44_claw_bridge




theorem gc44_claw_core : gc39_ThreeColouringCountIneq gc40_clawEnds (0 : Fin 4) 1 2 3 :=
  gc44_countIneq_of_forest gc40_clawEnds gc40_clawEnds_loopless
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    gc40_clawEnds_univ_sources gc44_claw_forest gc44_claw_bridge





theorem gc44_reloc_applies_claw :
    (∀ i : Fin 3, ¬ (gc40_clawEnds i).IsDiag)
      ∧ ((0 : Fin 4) ≠ 1 ∧ (0 : Fin 4) ≠ 2 ∧ (0 : Fin 4) ≠ 3
          ∧ (1 : Fin 4) ≠ 2 ∧ (1 : Fin 4) ≠ 3 ∧ (2 : Fin 4) ≠ 3)
      ∧ sources gc40_clawEnds (univ : Finset (Fin 3)) = ({0, 1, 2, 3} : Finset (Fin 4))
      ∧ gc44_ForestHyp gc40_clawEnds
      ∧ gc44_DisjointBridge gc40_clawEnds (0 : Fin 4) 1 2 3 :=
  ⟨gc40_clawEnds_loopless, ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩,
    gc40_clawEnds_univ_sources, gc44_claw_forest, gc44_claw_bridge⟩

end StatMech.Walls
