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
import Code.Walls.gc88brereroutehall

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









theorem gc89b_reroute_boundary_empty (ends : ι → Sym2 W) {K₁ P : Finset ι} (hP : P ⊆ K₁)
    {o g : W} (hK₁ : sources ends K₁ = ({o, g} : Finset W)) (hPsrc : sources ends P = ({o, g} : Finset W)) :
    sources ends (K₁ \ P) = (∅ : Finset W) := by
  have hsd : K₁ \ P = K₁ ∆ P := by
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_symmDiff]
    constructor
    · rintro ⟨ha, hna⟩; exact Or.inl ⟨ha, hna⟩
    · rintro (⟨ha, hna⟩ | ⟨ha, hna⟩)
      · exact ⟨ha, hna⟩
      · exact absurd (hP ha) hna
  rw [hsd, sources_symmDiff, hK₁, hPsrc, symmDiff_self, Finset.bot_eq_empty]



theorem gc89b_complement_union (m K₁ P : Finset ι) (hK₁m : K₁ ⊆ m) (hP : P ⊆ K₁) :
    m \ (K₁ \ P) = (m \ K₁) ∪ P := by
  ext a
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨ham, hna⟩
    by_cases hP' : a ∈ P
    · exact Or.inr hP'
    · exact Or.inl ⟨ham, fun hK => hna ⟨hK, hP'⟩⟩
  · rintro (⟨ham, hnK⟩ | hP')
    · exact ⟨ham, fun h => hnK h.1⟩
    · exact ⟨hK₁m (hP hP'), fun h => h.2 hP'⟩



theorem gc89b_reroute_complement_sources (ends : ι → Sym2 W) {m K₁ P : Finset ι} (hK₁m : K₁ ⊆ m)
    (hP : P ⊆ K₁) {o g : W} (hK₁ : sources ends K₁ = ({o, g} : Finset W))
    (hPsrc : sources ends P = ({o, g} : Finset W)) :
    sources ends (m \ (K₁ \ P)) = sources ends m := by
  have hJ₁m : K₁ \ P ⊆ m := (Finset.sdiff_subset).trans hK₁m
  have hJ₁src : sources ends (K₁ \ P) = ∅ := gc89b_reroute_boundary_empty ends hP hK₁ hPsrc
  exact gc86b_sources_sdiff_of_empty ends hJ₁m hJ₁src
















theorem gc89b_conn_og (ends : ι → Sym2 W) {m K₁ P : Finset ι} (hK₁m : K₁ ⊆ m) (hP : P ⊆ K₁)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o g : W}
    (hPsrc : sources ends P = ({o, g} : Finset W)) (hog : o ≠ g) :
    connK ends (m \ (K₁ \ P)) o g := by
  
  have hPnd : ∀ i ∈ P, ¬ (ends i).IsDiag := fun i hi => hnd i (hK₁m (hP hi))
  have ho_odd : Odd (degK ends P o) := by rw [← RandomCurrent.mem_sources, hPsrc]; simp
  have hbdry : ∀ w, Odd (degK ends P w) → w = o ∨ w = g := by
    intro w hw
    have : w ∈ sources ends P := by rw [RandomCurrent.mem_sources]; exact hw
    rw [hPsrc] at this
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  have hconnP : connK ends P o g := RandomCurrent.path_exists ends P hPnd o g ho_odd hbdry hog
  
  have hPR : P ⊆ m \ (K₁ \ P) := by
    rw [gc89b_complement_union m K₁ P hK₁m hP]; exact Finset.subset_union_right
  exact gc87b_connK_mono ends hPR hconnP



theorem gc89b_conn_xg (ends : ι → Sym2 W) {m K₁ P : Finset ι} (hK₁m : K₁ ⊆ m) (hP : P ⊆ K₁)
    {x g : W} (hxg : connK ends (m \ K₁) x g) :
    connK ends (m \ (K₁ \ P)) x g := by
  have hsub : m \ K₁ ⊆ m \ (K₁ \ P) := by
    rw [gc89b_complement_union m K₁ P hK₁m hP]; exact Finset.subset_union_left
  exact gc87b_connK_mono ends hsub hxg














theorem gc89b_reroute_lands_allConn (ends : ι → Sym2 W) {m K₁ P : Finset ι} (hK₁m : K₁ ⊆ m)
    (hP : P ⊆ K₁) (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxne : x ≠ y) (hxg' : x ≠ g) (hyg : y ≠ g)
    (hK₁ : sources ends K₁ = ({o, g} : Finset W)) (hPsrc : sources ends P = ({o, g} : Finset W))
    (hxg : connK ends (m \ K₁) x g) :
    connK ends (m \ (K₁ \ P)) o x ∧ connK ends (m \ (K₁ \ P)) o y ∧ connK ends (m \ (K₁ \ P)) o g := by
  set R := m \ (K₁ \ P) with hR
  
  have hRnd : ∀ i ∈ R, ¬ (ends i).IsDiag := fun i hi => hnd i (Finset.mem_sdiff.1 hi).1
  have hRsrc : sources ends R = ({o, x, y, g} : Finset W) := by
    rw [hR, gc89b_reroute_complement_sources ends hK₁m hP hK₁ hPsrc, hsrc]
  
  have hcog : connK ends R o g := gc89b_conn_og ends hK₁m hP hnd hPsrc hog
  have hcxg : connK ends R x g := gc89b_conn_xg ends hK₁m hP hxg
  
  have hcox : connK ends R o x := hcog.trans (connK_symm ends R hcxg)
  refine ⟨hcox, ?_, hcog⟩
  
  
  have hodd_iff : ∀ w, Odd (degK ends R w) ↔ w ∈ ({o, x, y, g} : Finset W) := by
    intro w; rw [← RandomCurrent.mem_sources, hRsrc]
  
  have hoC : o ∈ compOf ends R o := by rw [RandomCurrent.mem_compOf]; exact Relation.ReflTransGen.refl
  have hxC : x ∈ compOf ends R o := by rw [RandomCurrent.mem_compOf]; exact hcox
  have hgC : g ∈ compOf ends R o := by rw [RandomCurrent.mem_compOf]; exact hcog
  
  have hsum_even := sum_deg_comp_even ends R hRnd o
  have hcount_even : Even (#((compOf ends R o).filter (fun v => Odd (degK ends R v)))) :=
    (RandomCurrent.even_sum_iff_even_count _ _).1 hsum_even
  
  have hoddo : Odd (degK ends R o) := (hodd_iff o).2 (by simp)
  have hoddx : Odd (degK ends R x) := (hodd_iff x).2 (by simp)
  have hoddg : Odd (degK ends R g) := (hodd_iff g).2 (by simp)
  set S := (compOf ends R o).filter (fun v => Odd (degK ends R v)) with hS
  have hoS : o ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨hoC, hoddo⟩
  have hxS : x ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨hxC, hoddx⟩
  have hgS : g ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨hgC, hoddg⟩
  
  have hS_sub : S ⊆ ({o, x, y, g} : Finset W) := by
    intro w hw
    rw [hS, Finset.mem_filter] at hw
    exact (hodd_iff w).1 hw.2
  
  
  by_contra hcon
  
  have hy_notin : y ∉ S := by
    rw [hS, Finset.mem_filter, RandomCurrent.mem_compOf]
    rintro ⟨hcy, _⟩; exact hcon hcy
  
  have hSeq : S = ({o, x, g} : Finset W) := by
    apply Finset.Subset.antisymm
    · intro w hw
      have hw4 := hS_sub hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw4 ⊢
      rcases hw4 with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact absurd hw hy_notin
      · exact Or.inr (Or.inr rfl)
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hoS
      · exact hxS
      · exact hgS
  
  have hcard3 : #S = 3 := by
    rw [hSeq]
    rw [Finset.card_insert_of_notMem (by simp [hox, hog]),
        Finset.card_insert_of_notMem (by simp [hxg']), Finset.card_singleton]
  rw [hcard3] at hcount_even
  exact (Nat.not_even_iff_odd.2 ⟨1, rfl⟩) hcount_even















theorem gc89b_canonical_map_lands (ends : ι → Sym2 W) {m K₁ P : Finset ι} (hK₁m : K₁ ⊆ m)
    (hP : P ⊆ K₁) (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxne : x ≠ y) (hxg' : x ≠ g) (hyg : y ≠ g)
    (hK₁ : sources ends K₁ = ({o, g} : Finset W)) (hPsrc : sources ends P = ({o, g} : Finset W))
    (hxg : connK ends (m \ K₁) x g) :
    (K₁ \ P) ⊆ m ∧ sources ends (K₁ \ P) = (∅ : Finset W)
      ∧ connK ends (m \ (K₁ \ P)) o x ∧ connK ends (m \ (K₁ \ P)) o y
      ∧ connK ends (m \ (K₁ \ P)) o g := by
  refine ⟨(Finset.sdiff_subset).trans hK₁m, gc89b_reroute_boundary_empty ends hP hK₁ hPsrc, ?_⟩
  exact gc89b_reroute_lands_allConn ends hK₁m hP hnd hsrc hox hoy hog hxne hxg' hyg hK₁ hPsrc hxg




theorem gc89b_exists_ogPath (ends : ι → Sym2 W) {m K₁ : Finset ι} (hK₁m : K₁ ⊆ m)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o g : W} (hog : o ≠ g)
    (hK₁ : sources ends K₁ = ({o, g} : Finset W)) :
    ∃ P ⊆ K₁, sources ends P = ({o, g} : Finset W) := by
  have hK₁nd : ∀ i ∈ K₁, ¬ (ends i).IsDiag := fun i hi => hnd i (hK₁m hi)
  have ho_odd : Odd (degK ends K₁ o) := by rw [← RandomCurrent.mem_sources, hK₁]; simp
  have hbdry : ∀ w, Odd (degK ends K₁ w) → w = o ∨ w = g := by
    intro w hw
    have : w ∈ sources ends K₁ := by rw [RandomCurrent.mem_sources]; exact hw
    rw [hK₁] at this
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  have hconn : connK ends K₁ o g := RandomCurrent.path_exists ends K₁ hK₁nd o g ho_odd hbdry hog
  obtain ⟨P, hPm, hPsrc⟩ := exists_conn_set ends K₁ hconn hog
  exact ⟨P, hPm, hPsrc⟩

















def gc89b_isSimplePath (ends : ι → Sym2 W) (D : Finset ι) (o g : W) : Prop :=
  sources ends D = ({o, g} : Finset W) ∧ ∀ w : W, degK ends D w ≤ 2






def gc89b_metricReroute (ends : ι → Sym2 W) (o x g : W) :
    (Finset ι × Finset ι) → (Finset ι × Finset ι) → Prop :=
  fun KK JJ => gc89b_isSimplePath ends (KK.1 ∆ JJ.1) o g
    ∧ sources ends (KK.2 ∆ JJ.2) = ({x, g} : Finset W)




def gc89b_ntEnds : Fin 5 → Sym2 (Fin 4) :=
  fun i => if i = 0 then s(0, 3) else if i = 1 then s(0, 3) else if i = 2 then s(1, 3)
    else if i = 3 then s(0, 3) else s(2, 3)



theorem gc89b_ntEnds_sources :
    sources gc89b_ntEnds (univ : Finset (Fin 5)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
  decide








theorem gc89b_metric_nontotal :
    
    sources gc89b_ntEnds (({0} : Finset (Fin 5)) ∆ ({1, 3} : Finset (Fin 5)))
        = ({0, 3} : Finset (Fin 4))
    
      ∧ ¬ gc89b_metricReroute gc89b_ntEnds 0 1 3
          (({0} : Finset (Fin 5)), ({2} : Finset (Fin 5)))
          (({1, 3} : Finset (Fin 5)), (∅ : Finset (Fin 5))) := by
  refine ⟨by decide, ?_⟩
  intro h
  obtain ⟨⟨_, hdeg⟩, _⟩ := h
  have := hdeg 3
  revert this; decide





















theorem gc89b_canonical_collision :
    
    
    (({1} : Finset (Fin 4)) \ ({1} : Finset (Fin 4)) = (∅ : Finset (Fin 4)))
      ∧ (({2} : Finset (Fin 4)) \ ({2} : Finset (Fin 4)) = (∅ : Finset (Fin 4)))
      ∧ sources gc88b_wredEnds ({1} : Finset (Fin 4)) = ({0, 3} : Finset (Fin 4))
      ∧ sources gc88b_wredEnds ({2} : Finset (Fin 4)) = ({0, 3} : Finset (Fin 4)) := by
  refine ⟨by decide, by decide, ?_, ?_⟩ <;> decide













theorem gc89b_tri_reroute_lands :
    sources gc87b_triEnds (({0} : Finset (Fin 3))) = ({0, 3} : Finset (Fin 4))
      ∧ ({0} : Finset (Fin 3)) \ ({0} : Finset (Fin 3)) = (∅ : Finset (Fin 3))
      ∧ connK gc87b_triEnds ((univ : Finset (Fin 3)) \ (∅ : Finset (Fin 3))) 0 1
      ∧ connK gc87b_triEnds ((univ : Finset (Fin 3)) \ (∅ : Finset (Fin 3))) 0 2
      ∧ connK gc87b_triEnds ((univ : Finset (Fin 3)) \ (∅ : Finset (Fin 3))) 0 3 := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · rw [Finset.sdiff_empty]
    refine Relation.ReflTransGen.head (b := (3 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩
      (Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩)
  · rw [Finset.sdiff_empty]
    refine Relation.ReflTransGen.head (b := (3 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩
      (Relation.ReflTransGen.single ⟨2, by decide, by decide, by decide, by decide⟩)
  · rw [Finset.sdiff_empty]
    exact Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩
















theorem gc89b_metric_status (ends : ι → Sym2 W) {m K₁ P : Finset ι} (hK₁m : K₁ ⊆ m)
    (hP : P ⊆ K₁) (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxne : x ≠ y) (hxg' : x ≠ g) (hyg : y ≠ g)
    (hK₁ : sources ends K₁ = ({o, g} : Finset W)) (hPsrc : sources ends P = ({o, g} : Finset W))
    (hxg : connK ends (m \ K₁) x g) :
    
    (sources ends (K₁ \ P) = (∅ : Finset W)
        ∧ connK ends (m \ (K₁ \ P)) o x ∧ connK ends (m \ (K₁ \ P)) o y
        ∧ connK ends (m \ (K₁ \ P)) o g)
    
    ∧ (∃ Q ⊆ K₁, sources ends Q = ({o, g} : Finset W)) := by
  refine ⟨⟨gc89b_reroute_boundary_empty ends hP hK₁ hPsrc, ?_⟩,
    gc89b_exists_ogPath ends hK₁m hnd hog hK₁⟩
  exact gc89b_reroute_lands_allConn ends hK₁m hP hnd hsrc hox hoy hog hxne hxg' hyg hK₁ hPsrc hxg



















theorem gc89b_machine_findings : True := trivial

end StatMech.Walls
