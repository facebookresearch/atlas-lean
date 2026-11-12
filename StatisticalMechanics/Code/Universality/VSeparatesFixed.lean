/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































import Mathlib
import Code.Lattice.Clusters
import Code.Lattice.CrossingParity
import Code.TwoDim.Crossings
import Code.RSW.Defs
import Code.RSW.Strip
import Code.Universality.Defs
import Code.Universality.RSWStrip
import Code.Universality.HVIntersection
import Code.Universality.VSeparates

open Set MeasureTheory SimpleGraph
open scoped ENNReal NNReal

namespace StatMech

namespace Universality

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip






























def vsFix_VSeparatesHFixed (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ) : Prop :=
  α ≤ m → m ≤ m' → m' ≤ β →
  ∀ (xB : Site 2) (hxB : xB ∈ rect m m' c d),
  
  
  xB ∈ bottomSide m m' c d →
  ∀ (yT : Site 2) (hyT : yT ∈ topSide m m' c d),
  ConnectedWithin 2 ω (rect m m' c d) ⟨xB, hxB⟩ ⟨yT, topSide_subset hyT⟩ →
  ∀ (x y : rect α β c d), (x : Site 2) 0 = α → (y : Site 2) 0 = β →
  ∀ (w : (openSubgraphInduce 2 ω (rect α β c d)).Walk x y),
    ∃ z ∈ w.support, (z : Site 2) ∈ overlapComp ω m m' c d xB hxB















theorem vsFix_hvMeet (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (hsep : vsFix_VSeparatesHFixed ω α β m m' c d) : HVMeetProperty ω α β m m' c d := by
  classical
  intro hαm hmm' hm'β xL yR hcH xB yT hcV
  
  have hxBmem : (xB : Site 2) ∈ rect m m' c d := bottomSide_subset xB.2
  
  obtain ⟨wH⟩ := hcH
  
  have hx0 : ((⟨(xL : Site 2), leftSide_subset xL.2⟩ : rect α β c d) : Site 2) 0 = α :=
    xL.2.2
  have hy0 : ((⟨(yR : Site 2), rightSide_subset yR.2⟩ : rect α β c d) : Site 2) 0 = β :=
    yR.2.2
  
  
  obtain ⟨z, hzs, hzP⟩ := hsep hαm hmm' hm'β (xB : Site 2) hxBmem xB.2 (yT : Site 2) yT.2
    hcV ⟨(xL : Site 2), leftSide_subset xL.2⟩ ⟨(yR : Site 2), rightSide_subset yR.2⟩
    hx0 hy0 wH
  obtain ⟨hzO, hzVconn⟩ := hzP
  
  exact ⟨(z : Site 2), hzO, z.2, ⟨wH.takeUntil z hzs⟩, hzVconn⟩









theorem vsFix_hvIntersection (ω : ConfigSpace (Sym2 (Site 2)))
    {a m m' b c d : ℤ} (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hsepL : vsFix_VSeparatesHFixed ω a m' m m' c d)
    (hsepR : vsFix_VSeparatesHFixed ω m b m m' c d) :
    HVIntersectionProperty ω a m m' b c d :=
  hvIntersection_of_meet ω ham hmm' hm'b
    (vsFix_hvMeet ω a m' m m' c d hsepL)
    (vsFix_hvMeet ω m b m m' c d hsepR)













theorem vsFix_rsw_strip_glue (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    [IsProbabilityMeasure μ] (hpa : PositivelyAssociated μ)
    {a m m' b c d : ℤ} (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (hsepL : ∀ ω, vsFix_VSeparatesHFixed ω a m' m m' c d)
    (hsepR : ∀ ω, vsFix_VSeparatesHFixed ω m b m m' c d) :
    μ.real (horizontalCrossingEvent a m' c d)
        * μ.real (verticalCrossingEvent m m' c d)
        * μ.real (horizontalCrossingEvent m b c d)
      ≤ μ.real (horizontalCrossingEvent a b c d) :=
  rsw_strip_glue_of_intersection μ hpa
    (fun ω => vsFix_hvIntersection ω ham hmm' hm'b (hsepL ω) (hsepR ω))


































def vsFix_arc_sides (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ) : Prop :=
  α ≤ m → m ≤ m' → m' ≤ β →
  ∀ (xB : Site 2) (hxB : xB ∈ rect m m' c d),
  xB ∈ bottomSide m m' c d →
  ∀ (yT : Site 2) (hyT : yT ∈ topSide m m' c d),
  ConnectedWithin 2 ω (rect m m' c d) ⟨xB, hxB⟩ ⟨yT, topSide_subset hyT⟩ →
  ∃ L : Set (Site 2),
    
    (∀ z : Site 2, z ∈ rect α β c d → z 0 = α → z ∈ L) ∧
    
    (∀ z : Site 2, z ∈ rect α β c d → z 0 = β → z ∉ L) ∧
    
    (∀ u v : Site 2, u ∈ rect α β c d → v ∈ rect α β c d →
        (hypercubicLattice 2).Adj u v → bdEdge L s(u, v) →
        u ∈ overlapComp ω m m' c d xB hxB ∨ v ∈ overlapComp ω m m' c d xB hxB)











theorem vsFix_arc_sides_imp (ω : ConfigSpace (Sym2 (Site 2))) (α β m m' c d : ℤ)
    (harc : vsFix_arc_sides ω α β m m' c d) :
    vsFix_VSeparatesHFixed ω α β m m' c d := by
  classical
  intro hαm hmm' hm'β xB hxB hxBbot yT hyT hcV x y hx0 hy0 wH
  
  obtain ⟨L, hLleft, hLright, hLedge⟩ := harc hαm hmm' hm'β xB hxB hxBbot yT hyT hcV
  
  set wL : (hypercubicLattice 2).Walk (x : Site 2) (y : Site 2) :=
    liftWalk ω (rect α β c d) wH with hwL
  
  have hxL : (x : Site 2) ∈ L := hLleft (x : Site 2) x.2 hx0
  have hyL : (y : Site 2) ∉ L := hLright (y : Site 2) y.2 hy0
  
  have hodd : ¬ Even (crossCount L wL) := by
    rw [crossCount_parity]
    intro h
    exact hyL (h.mp hxL)
  
  have hbd : ∃ e ∈ wL.edges, bdEdge L e := by
    by_contra hcon
    apply hodd
    have hz : crossCount L wL = 0 := by
      rw [crossCount, List.countP_eq_zero]
      intro e he
      simp only [decide_eq_true_eq]
      exact fun hb => hcon ⟨e, he, hb⟩
    rw [hz]; exact ⟨0, rfl⟩
  obtain ⟨e, hemem, hebd⟩ := hbd
  
  
  induction e with
  | h u v =>
    
    
    have hu_supp : u ∈ wL.support := wL.fst_mem_support_of_mem_edges hemem
    have hv_supp : v ∈ wL.support := wL.snd_mem_support_of_mem_edges hemem
    obtain ⟨u', hu'_mem, hu'_eq⟩ := liftWalk_support_mem ω (rect α β c d) wH hu_supp
    obtain ⟨v', hv'_mem, hv'_eq⟩ := liftWalk_support_mem ω (rect α β c d) wH hv_supp
    have hu_box : u ∈ rect α β c d := hu'_eq ▸ u'.2
    have hv_box : v ∈ rect α β c d := hv'_eq ▸ v'.2
    
    have huv_adj : (hypercubicLattice 2).Adj u v := wL.adj_of_mem_edges hemem
    
    rcases hLedge u v hu_box hv_box huv_adj hebd with hUcomp | hVcomp
    · 
      exact ⟨u', hu'_mem, hu'_eq ▸ hUcomp⟩
    · 
      exact ⟨v', hv'_mem, hv'_eq ▸ hVcomp⟩








theorem vsFix_rsw_strip_glue_of_arc_sides (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    [IsProbabilityMeasure μ] (hpa : PositivelyAssociated μ)
    {a m m' b c d : ℤ} (ham : a ≤ m) (hmm' : m ≤ m') (hm'b : m' ≤ b)
    (harcL : ∀ ω, vsFix_arc_sides ω a m' m m' c d)
    (harcR : ∀ ω, vsFix_arc_sides ω m b m m' c d) :
    μ.real (horizontalCrossingEvent a m' c d)
        * μ.real (verticalCrossingEvent m m' c d)
        * μ.real (horizontalCrossingEvent m b c d)
      ≤ μ.real (horizontalCrossingEvent a b c d) :=
  vsFix_rsw_strip_glue μ hpa ham hmm' hm'b
    (fun ω => vsFix_arc_sides_imp ω a m' m m' c d (harcL ω))
    (fun ω => vsFix_arc_sides_imp ω m b m m' c d (harcR ω))

end Universality

end StatMech
