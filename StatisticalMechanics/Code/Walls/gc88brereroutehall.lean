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












noncomputable def gc88b_cogxgSet (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    Finset (Finset ι × Finset ι) :=
  (m.powerset ×ˢ m.powerset).filter
    (fun KK => Disjoint KK.1 KK.2 ∧ sources ends KK.1 = ({o, g} : Finset W)
      ∧ sources ends KK.2 = ({x, g} : Finset W))




noncomputable def gc88b_T3Set (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    Finset (Finset ι × Finset ι) :=
  (m.powerset ×ˢ m.powerset).filter
    (fun JJ => Disjoint JJ.1 JJ.2 ∧ sources ends JJ.1 = (∅ : Finset W)
      ∧ sources ends JJ.2 = (∅ : Finset W)
      ∧ connK ends (m \ JJ.1) o x ∧ connK ends (m \ JJ.1) o y ∧ connK ends (m \ JJ.1) o g)


theorem gc88b_cogxgSet_card (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    #(gc88b_cogxgSet ends m o x y g) = gc85b_pcount ends m {o, g} {x, g} := rfl





theorem gc88b_T3Set_card (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    #(gc88b_T3Set ends m o x y g) = gc87b_T3 ends m o x y g := by
  unfold gc88b_T3Set gc87b_T3
  rw [Finset.card_eq_sum_card_fiberwise
        (f := fun JJ => JJ.1)
        (t := (m.powerset.filter (fun K => sources ends K = ∅)).filter
          (fun J₁ => connK ends (m \ J₁) o x ∧ connK ends (m \ J₁) o y ∧ connK ends (m \ J₁) o g))
        (fun JJ hJJ => by
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
            Finset.mem_powerset] at hJJ ⊢
          exact ⟨⟨hJJ.1.1, hJJ.2.2.1⟩, hJJ.2.2.2.2⟩)]
  refine Finset.sum_congr rfl (fun J₁ hJ₁ => ?_)
  simp only [Finset.mem_filter, Finset.mem_powerset] at hJ₁
  obtain ⟨⟨hJ₁m, hJ₁src⟩, hconn⟩ := hJ₁
  
  unfold gc86b_ncount
  symm
  apply Finset.card_bij (fun J₂ _ => (J₁, J₂))
  · intro J₂ hJ₂
    simp only [Finset.mem_filter, Finset.mem_powerset] at hJ₂
    obtain ⟨hJ₂sub, hJ₂src⟩ := hJ₂
    have hJ₂m : J₂ ⊆ m := hJ₂sub.trans Finset.sdiff_subset
    have hdis : Disjoint J₁ J₂ := by
      rw [Finset.disjoint_left]
      intro a haJ₁ haJ₂
      exact (Finset.mem_sdiff.1 (hJ₂sub haJ₂)).2 haJ₁
    rw [Finset.mem_filter]
    refine ⟨?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset]
    exact ⟨⟨hJ₁m, hJ₂m⟩, hdis, hJ₁src, hJ₂src, hconn.1, hconn.2.1, hconn.2.2⟩
  · intro J₂ hJ₂ J₂' hJ₂' h
    simp only [Prod.mk.injEq] at h
    exact h.2
  · rintro ⟨L₁, L₂⟩ hLL
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hLL
    obtain ⟨⟨⟨hL₁m, hL₂m⟩, hdis, hL₁src, hL₂src, _⟩, hproj⟩ := hLL
    
    subst hproj
    refine ⟨L₂, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, hL₂src⟩
    intro a ha
    rw [Finset.mem_sdiff]
    exact ⟨hL₂m ha, fun hL₁ => (Finset.disjoint_left.1 hdis) hL₁ ha⟩













def gc88b_reroute (ends : ι → Sym2 W) (o g : W) :
    (Finset ι × Finset ι) → (Finset ι × Finset ι) → Prop :=
  fun KK JJ => sources ends (KK.1 ∆ JJ.1) = ({o, g} : Finset W)









theorem gc88b_reroute_total (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W)
    {KK JJ : Finset ι × Finset ι} (hKK : KK ∈ gc88b_cogxgSet ends m o x y g)
    (hJJ : JJ ∈ gc88b_T3Set ends m o x y g) :
    gc88b_reroute ends o g KK JJ := by
  simp only [gc88b_cogxgSet, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hKK
  simp only [gc88b_T3Set, Finset.mem_filter, Finset.mem_product, Finset.mem_powerset] at hJJ
  have hK₁ : sources ends KK.1 = ({o, g} : Finset W) := hKK.2.2.1
  have hJ₁ : sources ends JJ.1 = (∅ : Finset W) := hJJ.2.2.1
  unfold gc88b_reroute
  rw [sources_symmDiff, hK₁, hJ₁, show (∅ : Finset W) = ⊥ from rfl, symmDiff_bot]














noncomputable def gc88b_nbr (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W)
    (KK : Finset ι × Finset ι) : Finset (Finset ι × Finset ι) :=
  (gc88b_T3Set ends m o x y g).filter (fun JJ => gc88b_reroute ends o g KK JJ)




theorem gc88b_nbr_eq_T3Set (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W)
    {KK : Finset ι × Finset ι} (hKK : KK ∈ gc88b_cogxgSet ends m o x y g) :
    gc88b_nbr ends m o x y g KK = gc88b_T3Set ends m o x y g := by
  unfold gc88b_nbr
  rw [Finset.filter_true_of_mem]
  intro JJ hJJ
  exact gc88b_reroute_total ends m o x y g hKK hJJ





noncomputable def gc88b_hallFamily (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    {KK // KK ∈ gc88b_cogxgSet ends m o x y g} → Finset (Finset ι × Finset ι) :=
  fun KK => gc88b_nbr ends m o x y g KK.1




def gc88b_Marriage (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) : Prop :=
  ∀ s : Finset {KK // KK ∈ gc88b_cogxgSet ends m o x y g},
    #s ≤ #(s.biUnion (gc88b_hallFamily ends m o x y g))



theorem gc88b_biUnion_eq_T3Set (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W)
    {s : Finset {KK // KK ∈ gc88b_cogxgSet ends m o x y g}} (hs : s.Nonempty) :
    s.biUnion (gc88b_hallFamily ends m o x y g) = gc88b_T3Set ends m o x y g := by
  apply Finset.Subset.antisymm
  · intro JJ hJJ
    rw [Finset.mem_biUnion] at hJJ
    obtain ⟨KK, hKKs, hJJnbr⟩ := hJJ
    rw [gc88b_hallFamily, gc88b_nbr_eq_T3Set ends m o x y g KK.2] at hJJnbr
    exact hJJnbr
  · intro JJ hJJ
    obtain ⟨KK, hKKs⟩ := hs
    rw [Finset.mem_biUnion]
    refine ⟨KK, hKKs, ?_⟩
    rw [gc88b_hallFamily, gc88b_nbr_eq_T3Set ends m o x y g KK.2]
    exact hJJ











theorem gc88b_marriage_iff_cogxg_le_T3 (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    gc88b_Marriage ends m o x y g ↔ gc87b_CogxgLeT3 ends m o x y g := by
  unfold gc88b_Marriage gc87b_CogxgLeT3
  rw [← gc88b_cogxgSet_card ends m o x y g, ← gc88b_T3Set_card ends m o x y g]
  constructor
  · 
    intro hM
    rcases (gc88b_cogxgSet ends m o x y g).eq_empty_or_nonempty with hemp | hne
    · rw [hemp]; simp
    · 
      have huniv := hM Finset.univ
      have hcard_univ : #(Finset.univ : Finset {KK // KK ∈ gc88b_cogxgSet ends m o x y g})
          = #(gc88b_cogxgSet ends m o x y g) := by
        rw [Finset.card_univ, Fintype.card_coe]
      
      obtain ⟨KK₀, hKK₀⟩ := hne
      have hunivne : (Finset.univ : Finset {KK // KK ∈ gc88b_cogxgSet ends m o x y g}).Nonempty :=
        ⟨⟨KK₀, hKK₀⟩, Finset.mem_univ _⟩
      rw [gc88b_biUnion_eq_T3Set ends m o x y g hunivne, hcard_univ] at huniv
      exact huniv
  · 
    intro hle s
    rcases s.eq_empty_or_nonempty with hemp | hne
    · rw [hemp]; simp
    · rw [gc88b_biUnion_eq_T3Set ends m o x y g hne]
      calc #s ≤ #(Finset.univ : Finset {KK // KK ∈ gc88b_cogxgSet ends m o x y g}) :=
              Finset.card_le_card (Finset.subset_univ s)
        _ = #(gc88b_cogxgSet ends m o x y g) := by rw [Finset.card_univ, Fintype.card_coe]
        _ ≤ #(gc88b_T3Set ends m o x y g) := hle












theorem gc88b_injection_of_marriage (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W)
    (hM : gc88b_Marriage ends m o x y g) :
    ∃ f : {KK // KK ∈ gc88b_cogxgSet ends m o x y g} → (Finset ι × Finset ι),
      Function.Injective f ∧ ∀ KK, f KK ∈ gc88b_hallFamily ends m o x y g KK :=
  (Finset.all_card_le_biUnion_card_iff_exists_injective
    (gc88b_hallFamily ends m o x y g)).1 hM






theorem gc88b_cogxg_le_T3_of_marriage_via_hall (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W)
    (hM : gc88b_Marriage ends m o x y g) :
    gc87b_CogxgLeT3 ends m o x y g := by
  obtain ⟨f, hfinj, hfmem⟩ := gc88b_injection_of_marriage ends m o x y g hM
  unfold gc87b_CogxgLeT3
  rw [← gc88b_cogxgSet_card ends m o x y g, ← gc88b_T3Set_card ends m o x y g]
  
  have himg : (Finset.univ : Finset {KK // KK ∈ gc88b_cogxgSet ends m o x y g}).image f
      ⊆ gc88b_T3Set ends m o x y g := by
    intro JJ hJJ
    rw [Finset.mem_image] at hJJ
    obtain ⟨KK, _, rfl⟩ := hJJ
    have := hfmem KK
    rwa [gc88b_hallFamily, gc88b_nbr_eq_T3Set ends m o x y g KK.2] at this
  calc #(gc88b_cogxgSet ends m o x y g)
        = #(Finset.univ : Finset {KK // KK ∈ gc88b_cogxgSet ends m o x y g}) := by
          rw [Finset.card_univ, Fintype.card_coe]
    _ = #((Finset.univ : Finset {KK // KK ∈ gc88b_cogxgSet ends m o x y g}).image f) := by
          rw [Finset.card_image_of_injective _ hfinj]
    _ ≤ #(gc88b_T3Set ends m o x y g) := Finset.card_le_card himg







theorem gc88b_close_of_marriage (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hM : gc88b_Marriage ends m o x y g) :
    gc85b_ThreeCurrentBijection ends m o x y g :=
  gc87b_bijection_of_cogxg_le_T3 ends m hnd hsrc hox hoy hog
    (gc88b_cogxg_le_T3_of_marriage_via_hall ends m o x y g hM)
















def gc88b_wredEnds : Fin 4 → Sym2 (Fin 4) :=
  fun i => if i = 0 then s(0, 1) else if i = 1 then s(0, 3) else if i = 2 then s(0, 3) else s(2, 3)


theorem gc88b_wred_sources :
    sources gc88b_wredEnds (univ : Finset (Fin 4)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
  decide




theorem gc88b_connK_color_invariant (ends : ι → Sym2 W) (K : Finset ι) (c : W → Bool)
    (hc : ∀ i ∈ K, ∀ a b : W, a ∈ ends i → b ∈ ends i → c a = c b) {a b : W}
    (h : connK ends K a b) : c a = c b := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      obtain ⟨i, hi, hpa, hpb, _⟩ := hstep
      rw [ih]; exact hc i hi _ _ hpa hpb






theorem gc88b_wred_cogxg_fibers_card :
    (((univ : Finset (Fin 4)).powerset.filter
        (fun K => sources gc88b_wredEnds K = ({0, 3} : Finset (Fin 4)))).filter
      (fun K₁ => connK gc88b_wredEnds ((univ : Finset (Fin 4)) \ K₁) 1 3))
      = ({{1}, {2}} : Finset (Finset (Fin 4))) := by
  
  
  have hbase : ((univ : Finset (Fin 4)).powerset.filter
      (fun K => sources gc88b_wredEnds K = ({0, 3} : Finset (Fin 4))))
      = ({{1}, {2}} : Finset (Finset (Fin 4))) := by decide
  rw [hbase]
  rw [Finset.filter_true_of_mem]
  intro K hK
  simp only [Finset.mem_insert, Finset.mem_singleton] at hK
  
  rcases hK with rfl | rfl
  · 
    refine Relation.ReflTransGen.head (b := (0 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩
      (Relation.ReflTransGen.single ⟨2, by decide, by decide, by decide, by decide⟩)
  · 
    refine Relation.ReflTransGen.head (b := (0 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩
      (Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩)






theorem gc88b_wred_T3_fibers_card :
    (((univ : Finset (Fin 4)).powerset.filter
        (fun K => sources gc88b_wredEnds K = (∅ : Finset (Fin 4)))).filter
      (fun J₁ => connK gc88b_wredEnds ((univ : Finset (Fin 4)) \ J₁) 0 1
        ∧ connK gc88b_wredEnds ((univ : Finset (Fin 4)) \ J₁) 0 2
        ∧ connK gc88b_wredEnds ((univ : Finset (Fin 4)) \ J₁) 0 3))
      = ({∅} : Finset (Finset (Fin 4))) := by
  have hbase : ((univ : Finset (Fin 4)).powerset.filter
      (fun K => sources gc88b_wredEnds K = (∅ : Finset (Fin 4))))
      = ({∅, {1, 2}} : Finset (Finset (Fin 4))) := by decide
  rw [hbase]
  ext J
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hJ | hJ, hconn⟩
    · exact hJ
    · 
      exfalso
      subst hJ
      
      have := gc88b_connK_color_invariant gc88b_wredEnds ((univ : Finset (Fin 4)) \ {1, 2})
        (fun v => decide (v = 0 ∨ v = 1)) (by decide) hconn.2.2
      simp at this
  · rintro rfl
    refine ⟨Or.inl rfl, ?_, ?_, ?_⟩
    
    · exact Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩
    · refine Relation.ReflTransGen.head (b := (3 : Fin 4))
        ⟨1, by decide, by decide, by decide, by decide⟩
        (Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩)
    · exact Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩








theorem gc88b_wred_fiber_injection_impossible :
    
    #(gc88b_cogxgSet gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3) = 2
      ∧ #(gc88b_T3Set gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3)
          = gc87b_T3 gc88b_wredEnds (univ : Finset (Fin 4)) 0 1 2 3
    
      ∧ #(((univ : Finset (Fin 4)).powerset.filter
            (fun K => sources gc88b_wredEnds K = ({0, 3} : Finset (Fin 4)))).filter
          (fun K₁ => connK gc88b_wredEnds ((univ : Finset (Fin 4)) \ K₁) 1 3))
        > #(((univ : Finset (Fin 4)).powerset.filter
            (fun K => sources gc88b_wredEnds K = (∅ : Finset (Fin 4)))).filter
          (fun J₁ => connK gc88b_wredEnds ((univ : Finset (Fin 4)) \ J₁) 0 1
            ∧ connK gc88b_wredEnds ((univ : Finset (Fin 4)) \ J₁) 0 2
            ∧ connK gc88b_wredEnds ((univ : Finset (Fin 4)) \ J₁) 0 3)) := by
  refine ⟨?_, gc88b_T3Set_card _ _ _ _ _ _, ?_⟩
  · unfold gc88b_cogxgSet; decide
  · rw [gc88b_wred_cogxg_fibers_card, gc88b_wred_T3_fibers_card]
    decide










theorem gc88b_tri_marriage :
    gc88b_Marriage gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3 :=
  (gc88b_marriage_iff_cogxg_le_T3 gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3).2
    (gc87b_tri_residue_nonvacuous.2)
















theorem gc88b_hall_status (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends m = ({o, x, y, g} : Finset W)) (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) :
    
    (∀ KK JJ, KK ∈ gc88b_cogxgSet ends m o x y g → JJ ∈ gc88b_T3Set ends m o x y g →
        gc88b_reroute ends o g KK JJ)
    
    ∧ (gc88b_Marriage ends m o x y g ↔ gc87b_CogxgLeT3 ends m o x y g)
    
    ∧ (gc88b_Marriage ends m o x y g → gc85b_ThreeCurrentBijection ends m o x y g) :=
  ⟨fun KK JJ hKK hJJ => gc88b_reroute_total ends m o x y g hKK hJJ,
   gc88b_marriage_iff_cogxg_le_T3 ends m o x y g,
   fun hM => gc88b_close_of_marriage ends m hnd hsrc hox hoy hog hM⟩
















theorem gc88b_machine_findings : True := trivial

end StatMech.Walls
