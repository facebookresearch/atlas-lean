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














theorem gc86b_o_connects_mark (ends : ι → Sym2 W) (R : Finset ι)
    (hnd : ∀ i ∈ R, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends R = ({o, x, y, g} : Finset W)) (ho : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) :
    connK ends R o x ∨ connK ends R o y ∨ connK ends R o g := by
  
  have ho_odd : Odd (degK ends R o) := by
    rw [← RandomCurrent.mem_sources, hsrc]; simp
  
  have hsum_even := sum_deg_comp_even ends R hnd o
  have hcount_even : Even (#((compOf ends R o).filter (fun v => Odd (degK ends R v)))) :=
    (RandomCurrent.even_sum_iff_even_count _ _).1 hsum_even
  have ho_in : o ∈ (compOf ends R o).filter (fun v => Odd (degK ends R v)) := by
    simp only [Finset.mem_filter, RandomCurrent.mem_compOf]
    exact ⟨Relation.ReflTransGen.refl, ho_odd⟩
  
  obtain ⟨w, hw_mem, hw_ne⟩ :
      ∃ w ∈ (compOf ends R o).filter (fun v => Odd (degK ends R v)), w ≠ o := by
    by_contra hcon
    push Not at hcon
    
    have hsingle : (compOf ends R o).filter (fun v => Odd (degK ends R v)) = {o} := by
      ext v
      simp only [Finset.mem_singleton]
      constructor
      · intro hv; exact hcon v hv
      · rintro rfl; exact ho_in
    rw [hsingle, Finset.card_singleton] at hcount_even
    exact (Nat.not_even_iff_odd.2 ⟨0, rfl⟩) hcount_even
  simp only [Finset.mem_filter, RandomCurrent.mem_compOf] at hw_mem
  obtain ⟨hconn_ow, hw_odd⟩ := hw_mem
  
  have hw_bdry : w ∈ ({o, x, y, g} : Finset W) := by
    rw [← hsrc, RandomCurrent.mem_sources]; exact hw_odd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw_bdry
  rcases hw_bdry with rfl | rfl | rfl | rfl
  · exact absurd rfl hw_ne
  · exact Or.inl hconn_ow
  · exact Or.inr (Or.inl hconn_ow)
  · exact Or.inr (Or.inr hconn_ow)










def gc86b_ncount (ends : ι → Sym2 W) (R : Finset ι) (A : Finset W) : ℕ :=
  #(R.powerset.filter (fun K => sources ends K = A))





theorem gc86b_ncount_conn_eq (ends : ι → Sym2 W) (R : Finset ι) {u v : W} (huv : u ≠ v)
    (hconn : connK ends R u v) :
    gc86b_ncount ends R {u, v} = gc86b_ncount ends R ∅ := by
  unfold gc86b_ncount
  obtain ⟨P, hPm, hPsrc⟩ := exists_conn_set ends R hconn huv
  have hbij := sources_shift_bijOn ends R P hPm (∅ : Finset W)
  rw [hPsrc, show (∅ : Finset W) = ⊥ from rfl, bot_symmDiff] at hbij
  
  have himg : (R.powerset.filter (fun K => sources ends K = ({u, v} : Finset W)))
      = (R.powerset.filter (fun K => sources ends K = ∅)).image (fun K => K ∆ P) := by
    ext K
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · intro ⟨hKm, hKsrc⟩
      obtain ⟨L, hL, hLK⟩ := hbij.2.2 ⟨hKm, hKsrc⟩
      exact ⟨L, ⟨hL.1, hL.2⟩, hLK⟩
    · rintro ⟨L, ⟨hLm, hLsrc⟩, rfl⟩
      have := hbij.1 ⟨hLm, hLsrc⟩
      exact ⟨this.1, this.2⟩
  rw [himg, Finset.card_image_of_injOn]
  intro K₁ hK₁ K₂ hK₂ h
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hK₁ hK₂
  exact hbij.2.1 ⟨hK₁.1, hK₁.2⟩ ⟨hK₂.1, hK₂.2⟩ h
















theorem gc86b_strong_of_conn (ends : ι → Sym2 W) (R : Finset ι)
    (hnd : ∀ i ∈ R, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends R = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) :
    gc86b_ncount ends R ∅
      ≤ gc86b_ncount ends R {o, x} + gc86b_ncount ends R {o, y} + gc86b_ncount ends R {o, g} := by
  rcases gc86b_o_connects_mark ends R hnd hsrc hox hoy hog with h | h | h
  · 
    have he := gc86b_ncount_conn_eq ends R hox h
    omega
  · 
    have he := gc86b_ncount_conn_eq ends R hoy h
    omega
  · 
    have he := gc86b_ncount_conn_eq ends R hog h
    omega
















theorem gc85b_pcount_fiber (ends : ι → Sym2 W) (m : Finset ι) (A B : Finset W) :
    gc85b_pcount ends m A B
      = ∑ K₁ ∈ m.powerset.filter (fun K => sources ends K = A),
          gc86b_ncount ends (m \ K₁) B := by
  unfold gc85b_pcount gc86b_ncount
  rw [Finset.card_eq_sum_card_fiberwise
        (f := fun KK => KK.1)
        (t := m.powerset.filter (fun K => sources ends K = A))
        (s := (m.powerset ×ˢ m.powerset).filter
          (fun KK => Disjoint KK.1 KK.2 ∧ sources ends KK.1 = A ∧ sources ends KK.2 = B))
        (fun KK hKK => by
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hKK
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset]
          exact ⟨hKK.1.1, hKK.2.2.1⟩)]
  refine Finset.sum_congr rfl (fun K₁ hK₁ => ?_)
  simp only [Finset.mem_filter, Finset.mem_powerset] at hK₁
  
  symm
  apply Finset.card_bij (fun K₂ _ => (K₁, K₂))
  · intro K₂ hK₂
    simp only [Finset.mem_filter, Finset.mem_powerset] at hK₂
    obtain ⟨hK₂sub, hK₂src⟩ := hK₂
    have hK₂m : K₂ ⊆ m := hK₂sub.trans (Finset.sdiff_subset)
    have hdis : Disjoint K₁ K₂ := by
      rw [Finset.disjoint_left]
      intro a haK₁ haK₂
      exact (Finset.mem_sdiff.1 (hK₂sub haK₂)).2 haK₁
    rw [Finset.mem_filter]
    refine ⟨?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨Finset.mem_powerset.2 hK₁.1, Finset.mem_powerset.2 hK₂m⟩, hdis, hK₁.2, hK₂src⟩
  · intro K₂ hK₂ K₂' hK₂' h
    simp only [Prod.mk.injEq] at h
    exact h.2
  · rintro ⟨L₁, L₂⟩ hLL
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hLL
    obtain ⟨⟨⟨hL₁m, hL₂m⟩, hdis, hL₁src, hL₂src⟩, hproj⟩ := hLL
    subst hproj
    refine ⟨L₂, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, hL₂src⟩
    intro a ha
    rw [Finset.mem_sdiff]
    exact ⟨hL₂m ha, fun hK₁ => (Finset.disjoint_left.1 hdis) hK₁ ha⟩









theorem gc86b_sources_sdiff_of_empty (ends : ι → Sym2 W) {m K₁ : Finset ι} (hK₁m : K₁ ⊆ m)
    (hK₁ : sources ends K₁ = ∅) :
    sources ends (m \ K₁) = sources ends m := by
  have hsd : m \ K₁ = m ∆ K₁ := by
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_symmDiff]
    constructor
    · rintro ⟨ham, haK₁⟩; exact Or.inl ⟨ham, haK₁⟩
    · rintro (⟨ham, haK₁⟩ | ⟨haK₁, ham⟩)
      · exact ⟨ham, haK₁⟩
      · exact absurd (hK₁m haK₁) ham
  rw [hsd, sources_symmDiff, hK₁, show (∅ : Finset W) = ⊥ from rfl, symmDiff_bot]












theorem gc86b_strong_global (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) :
    gc85b_pcount ends m ∅ ∅
      ≤ gc85b_pcount ends m ∅ {o, g} + gc85b_pcount ends m ∅ {o, x} + gc85b_pcount ends m ∅ {o, y} := by
  rw [gc85b_pcount_fiber ends m ∅ ∅, gc85b_pcount_fiber ends m ∅ {o, g},
      gc85b_pcount_fiber ends m ∅ {o, x}, gc85b_pcount_fiber ends m ∅ {o, y},
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun K₁ hK₁ => ?_)
  simp only [Finset.mem_filter, Finset.mem_powerset] at hK₁
  obtain ⟨hK₁m, hK₁src⟩ := hK₁
  
  have hRsrc : sources ends (m \ K₁) = ({o, x, y, g} : Finset W) := by
    rw [gc86b_sources_sdiff_of_empty ends hK₁m hK₁src, hsrc]
  have hRnd : ∀ i ∈ m \ K₁, ¬ (ends i).IsDiag := fun i hi => hnd i (Finset.mem_sdiff.1 hi).1
  
  have hstrong := gc86b_strong_of_conn ends (m \ K₁) hRnd hRsrc hox hoy hog
  
  omega


























def gc86b_CogxgResidual (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) : Prop :=
  2 * (gc85b_pcount ends m {o, g} {x, g} : ℤ)
    ≤ ((gc85b_pcount ends m ∅ {o, g} : ℤ) + (gc85b_pcount ends m ∅ {o, x} : ℤ)
        + (gc85b_pcount ends m ∅ {o, y} : ℤ)) - (gc85b_pcount ends m ∅ ∅ : ℤ)





theorem gc86b_bijection_iff_residual (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    gc85b_ThreeCurrentBijection ends m o x y g ↔ gc86b_CogxgResidual ends m o x y g := by
  unfold gc85b_ThreeCurrentBijection gc86b_CogxgResidual
  constructor
  · intro h; zify at h ⊢; omega
  · intro h; zify; omega






theorem gc86b_bijection_of_residual (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W)
    (hres : gc86b_CogxgResidual ends m o x y g) :
    gc85b_ThreeCurrentBijection ends m o x y g :=
  (gc86b_bijection_iff_residual ends m o x y g).2 hres











def gc86b_starEnds : Fin 4 → Sym2 (Fin 5) :=
  fun i => s(i.castSucc, (4 : Fin 5))



theorem gc86b_star_sources :
    sources gc86b_starEnds (univ : Finset (Fin 4)) = ({0, 1, 2, 3} : Finset (Fin 5)) := by
  decide




theorem gc86b_star_bijection :
    gc85b_ThreeCurrentBijection gc86b_starEnds (univ : Finset (Fin 4)) 0 1 2 3
      ∧ gc85b_pcount gc86b_starEnds (univ : Finset (Fin 4)) ∅ ∅ = 1 := by
  refine ⟨?_, ?_⟩
  · unfold gc85b_ThreeCurrentBijection gc85b_pcount; decide
  · unfold gc85b_pcount; decide























theorem gc86b_reroute_status (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) :
    
    (connK ends m o x ∨ connK ends m o y ∨ connK ends m o g)
    
    ∧ (gc85b_pcount ends m ∅ ∅
        ≤ gc85b_pcount ends m ∅ {o, g} + gc85b_pcount ends m ∅ {o, x} + gc85b_pcount ends m ∅ {o, y})
    
    ∧ (gc86b_CogxgResidual ends m o x y g ↔ gc85b_ThreeCurrentBijection ends m o x y g) :=
  ⟨gc86b_o_connects_mark ends m hnd hsrc hox hoy hog,
   gc86b_strong_global ends m hnd hsrc hox hoy hog,
   (gc86b_bijection_iff_residual ends m o x y g).symm⟩

end StatMech.Walls
