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
import Code.Walls.gc89bmetricinjection
import Code.Walls.gc90bperfiberinject

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
















noncomputable def gc91b_cogxgPairs (ends : ι → Sym2 W) (m : Finset ι) (o x g : W) :
    Finset (Finset ι × Finset ι) :=
  (m.powerset ×ˢ m.powerset).filter
    (fun KK => Disjoint KK.1 KK.2 ∧ sources ends KK.1 = ({o, g} : Finset W)
      ∧ sources ends KK.2 = (∅ : Finset W) ∧ connK ends (m \ KK.1) x g)




noncomputable def gc91b_T3Pairs (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    Finset (Finset ι × Finset ι) :=
  (m.powerset ×ˢ m.powerset).filter
    (fun JJ => Disjoint JJ.1 JJ.2 ∧ sources ends JJ.1 = (∅ : Finset W)
      ∧ sources ends JJ.2 = (∅ : Finset W)
      ∧ connK ends (m \ JJ.1) o x ∧ connK ends (m \ JJ.1) o y ∧ connK ends (m \ JJ.1) o g)












theorem gc91b_ncount_eq_disjoint_count (ends : ι → Sym2 W) {m K₁ : Finset ι} (hK₁m : K₁ ⊆ m) :
    gc86b_ncount ends (m \ K₁) ∅
      = #(m.powerset.filter (fun K₂ => Disjoint K₁ K₂ ∧ sources ends K₂ = (∅ : Finset W))) := by
  unfold gc86b_ncount
  apply Finset.card_bij (fun K₂ _ => K₂)
  · intro K₂ hK₂
    simp only [Finset.mem_filter, Finset.mem_powerset] at hK₂ ⊢
    obtain ⟨hK₂sub, hK₂src⟩ := hK₂
    refine ⟨hK₂sub.trans Finset.sdiff_subset, ?_, hK₂src⟩
    rw [Finset.disjoint_left]
    intro a haK₁ haK₂
    exact (Finset.mem_sdiff.1 (hK₂sub haK₂)).2 haK₁
  · intro K₂ _ K₂' _ h; exact h
  · intro K₂ hK₂
    simp only [Finset.mem_filter, Finset.mem_powerset] at hK₂
    obtain ⟨hK₂m, hdis, hK₂src⟩ := hK₂
    refine ⟨K₂, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, hK₂src⟩
    intro a ha
    rw [Finset.mem_sdiff]
    exact ⟨hK₂m ha, fun hK₁ => (Finset.disjoint_left.1 hdis) hK₁ ha⟩






theorem gc91b_cogxg_eq_card_pairs (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W} (hxg : x ≠ g) :
    gc85b_pcount ends m {o, g} {x, g} = #(gc91b_cogxgPairs ends m o x g) := by
  rw [gc87b_cogxg_fiber_conn (o := o) (x := x) (y := y) (g := g) ends m hnd hxg]
  
  rw [Finset.sum_congr rfl (fun K₁ hK₁ => by
        simp only [Finset.mem_filter, Finset.mem_powerset] at hK₁
        exact gc91b_ncount_eq_disjoint_count ends hK₁.1.1)]
  
  unfold gc91b_cogxgPairs
  rw [Finset.card_eq_sum_card_fiberwise
        (f := fun KK => KK.1)
        (t := (m.powerset.filter (fun K => sources ends K = ({o, g} : Finset W))).filter
          (fun K₁ => connK ends (m \ K₁) x g))
        (s := (m.powerset ×ˢ m.powerset).filter
          (fun KK => Disjoint KK.1 KK.2 ∧ sources ends KK.1 = ({o, g} : Finset W)
            ∧ sources ends KK.2 = (∅ : Finset W) ∧ connK ends (m \ KK.1) x g))
        (fun KK hKK => by
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hKK
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter, Finset.mem_powerset]
          exact ⟨⟨hKK.1.1, hKK.2.2.1⟩, hKK.2.2.2.2⟩)]
  refine Finset.sum_congr rfl (fun K₁ hK₁ => ?_)
  simp only [Finset.mem_filter, Finset.mem_powerset] at hK₁
  
  apply Finset.card_bij (fun K₂ _ => (K₁, K₂))
  · intro K₂ hK₂
    simp only [Finset.mem_filter, Finset.mem_powerset] at hK₂
    obtain ⟨hK₂m, hdis, hK₂src⟩ := hK₂
    rw [Finset.mem_filter]
    refine ⟨?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset]
    exact ⟨⟨hK₁.1.1, hK₂m⟩, hdis, hK₁.1.2, hK₂src, hK₁.2⟩
  · intro K₂ _ K₂' _ h
    simp only [Prod.mk.injEq] at h; exact h.2
  · rintro ⟨L₁, L₂⟩ hLL
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hLL
    obtain ⟨⟨⟨hL₁m, hL₂m⟩, hdis, hL₁src, hL₂src, hconn⟩, hproj⟩ := hLL
    subst hproj
    refine ⟨L₂, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hL₂m, hdis, hL₂src⟩






theorem gc91b_T3_eq_card_pairs (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    gc87b_T3 ends m o x y g = #(gc91b_T3Pairs ends m o x y g) := by
  unfold gc87b_T3
  rw [Finset.sum_congr rfl (fun J₁ hJ₁ => by
        simp only [Finset.mem_filter, Finset.mem_powerset] at hJ₁
        exact gc91b_ncount_eq_disjoint_count ends hJ₁.1.1)]
  unfold gc91b_T3Pairs
  rw [Finset.card_eq_sum_card_fiberwise
        (f := fun JJ => JJ.1)
        (t := (m.powerset.filter (fun K => sources ends K = (∅ : Finset W))).filter
          (fun J₁ => connK ends (m \ J₁) o x ∧ connK ends (m \ J₁) o y ∧ connK ends (m \ J₁) o g))
        (s := (m.powerset ×ˢ m.powerset).filter
          (fun JJ => Disjoint JJ.1 JJ.2 ∧ sources ends JJ.1 = (∅ : Finset W)
            ∧ sources ends JJ.2 = (∅ : Finset W)
            ∧ connK ends (m \ JJ.1) o x ∧ connK ends (m \ JJ.1) o y ∧ connK ends (m \ JJ.1) o g))
        (fun JJ hJJ => by
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hJJ
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter, Finset.mem_powerset]
          exact ⟨⟨hJJ.1.1, hJJ.2.2.1⟩, hJJ.2.2.2.2⟩)]
  refine Finset.sum_congr rfl (fun J₁ hJ₁ => ?_)
  simp only [Finset.mem_filter, Finset.mem_powerset] at hJ₁
  apply Finset.card_bij (fun J₂ _ => (J₁, J₂))
  · intro J₂ hJ₂
    simp only [Finset.mem_filter, Finset.mem_powerset] at hJ₂
    obtain ⟨hJ₂m, hdis, hJ₂src⟩ := hJ₂
    rw [Finset.mem_filter]
    refine ⟨?_, rfl⟩
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset]
    exact ⟨⟨hJ₁.1.1, hJ₂m⟩, hdis, hJ₁.1.2, hJ₂src, hJ₁.2.1, hJ₁.2.2.1, hJ₁.2.2.2⟩
  · intro J₂ _ J₂' _ h
    simp only [Prod.mk.injEq] at h; exact h.2
  · rintro ⟨L₁, L₂⟩ hLL
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hLL
    obtain ⟨⟨⟨hL₁m, hL₂m⟩, hdis, hL₁src, hL₂src, hc1, hc2, hc3⟩, hproj⟩ := hLL
    subst hproj
    refine ⟨L₂, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hL₂m, hdis, hL₂src⟩











theorem gc91b_cogxg_le_T3_of_injection (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W} (hxg : x ≠ g)
    (f : Finset ι × Finset ι → Finset ι × Finset ι)
    (hmaps : ∀ KK ∈ gc91b_cogxgPairs ends m o x g, f KK ∈ gc91b_T3Pairs ends m o x y g)
    (hinj : Set.InjOn f (gc91b_cogxgPairs ends m o x g)) :
    gc87b_CogxgLeT3 ends m o x y g := by
  unfold gc87b_CogxgLeT3
  rw [gc91b_cogxg_eq_card_pairs (o := o) (x := x) (y := y) (g := g) ends m hnd hxg,
      gc91b_T3_eq_card_pairs ends m o x y g]
  exact Finset.card_le_card_of_injOn f hmaps hinj








theorem gc91b_close_of_injection (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxg : x ≠ g)
    (f : Finset ι × Finset ι → Finset ι × Finset ι)
    (hmaps : ∀ KK ∈ gc91b_cogxgPairs ends m o x g, f KK ∈ gc91b_T3Pairs ends m o x y g)
    (hinj : Set.InjOn f (gc91b_cogxgPairs ends m o x g)) :
    gc85b_ThreeCurrentBijection ends m o x y g :=
  gc87b_bijection_of_cogxg_le_T3 ends m hnd hsrc hox hoy hog
    (gc91b_cogxg_le_T3_of_injection ends m hnd hxg f hmaps hinj)























theorem gc91b_boundary_reroute_total (ends : ι → Sym2 W) (m : Finset ι) {o x y g : W}
    {KK JJ : Finset ι × Finset ι} (hKK : KK ∈ gc91b_cogxgPairs ends m o x g)
    (hJJ : JJ ∈ gc91b_T3Pairs ends m o x y g) :
    sources ends (KK.1 ∆ JJ.1) = ({o, g} : Finset W) := by
  simp only [gc91b_cogxgPairs, gc91b_T3Pairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_powerset] at hKK hJJ
  have hK₁ : sources ends KK.1 = ({o, g} : Finset W) := hKK.2.2.1
  have hJ₁ : sources ends JJ.1 = (∅ : Finset W) := hJJ.2.2.1
  rw [sources_symmDiff, hK₁, hJ₁, show (∅ : Finset W) = ⊥ from rfl, symmDiff_bot]









theorem gc91b_boundary_marriage_iff (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W} (hxg : x ≠ g) :
    Nonempty ({KK // KK ∈ gc91b_cogxgPairs ends m o x g}
        ↪ {JJ // JJ ∈ gc91b_T3Pairs ends m o x y g})
      ↔ gc87b_CogxgLeT3 ends m o x y g := by
  unfold gc87b_CogxgLeT3
  rw [gc91b_cogxg_eq_card_pairs (o := o) (x := x) (y := y) (g := g) ends m hnd hxg,
      gc91b_T3_eq_card_pairs ends m o x y g]
  rw [← Fintype.card_coe (gc91b_cogxgPairs ends m o x g),
      ← Fintype.card_coe (gc91b_T3Pairs ends m o x y g)]
  constructor
  · rintro ⟨e⟩; exact Fintype.card_le_of_embedding e
  · intro h; exact Function.Embedding.nonempty_of_card_le h



















theorem gc91b_star_boundary_total :
    
    sources gc90b_starEnds ({2} : Finset (Fin 5)) = ({0, 3} : Finset (Fin 4))
    
      ∧ sources gc90b_starEnds ({2, 3} : Finset (Fin 5)) = (∅ : Finset (Fin 4))
      ∧ ¬ (({2, 3} : Finset (Fin 5)) ⊆ ({2} : Finset (Fin 5)))
    
      ∧ sources gc90b_starEnds (({2} : Finset (Fin 5)) ∆ ({2, 3} : Finset (Fin 5)))
          = ({0, 3} : Finset (Fin 4)) := by
  refine ⟨by decide, by decide, by decide, by decide⟩




















theorem gc91b_global_status (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxg : x ≠ g) :
    
    (gc85b_pcount ends m {o, g} {x, g} = #(gc91b_cogxgPairs ends m o x g)
        ∧ gc87b_T3 ends m o x y g = #(gc91b_T3Pairs ends m o x y g))
    
    ∧ (∀ f : Finset ι × Finset ι → Finset ι × Finset ι,
        (∀ KK ∈ gc91b_cogxgPairs ends m o x g, f KK ∈ gc91b_T3Pairs ends m o x y g) →
        Set.InjOn f (gc91b_cogxgPairs ends m o x g) →
        gc85b_ThreeCurrentBijection ends m o x y g)
    
    ∧ (∀ {KK JJ : Finset ι × Finset ι}, KK ∈ gc91b_cogxgPairs ends m o x g →
        JJ ∈ gc91b_T3Pairs ends m o x y g →
        sources ends (KK.1 ∆ JJ.1) = ({o, g} : Finset W)) := by
  refine ⟨⟨gc91b_cogxg_eq_card_pairs (o := o) (x := x) (y := y) (g := g) ends m hnd hxg,
      gc91b_T3_eq_card_pairs ends m o x y g⟩, ?_, ?_⟩
  · intro f hmaps hinj
    exact gc91b_close_of_injection ends m hnd hsrc hox hoy hog hxg f hmaps hinj
  · intro KK JJ hKK hJJ
    exact gc91b_boundary_reroute_total ends m hKK hJJ























theorem gc91b_machine_findings : True := trivial

end StatMech.Walls
