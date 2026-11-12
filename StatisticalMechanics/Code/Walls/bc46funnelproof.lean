/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.BoxSurfaceVolume
import Code.Lattice.Clusters
import Code.Percolation.BurtonKeane
import Code.Percolation.BurtonKeaneUniqueness
import Code.Percolation.TrifurcationCount
import Code.Percolation.DisjointArmEndsProve
import Code.Percolation.DisjointArmEndsProve2
import Code.Percolation.BKForestLib
import Code.Walls.bc37armadj
import Code.Walls.bc39spanning
import Code.Walls.bc40funnel
import Code.Walls.bc45depthwalk

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}











theorem bc46_openEdge_removeSite_of_ne (t : Site d) (ω : ConfigSpace (Sym2 (Site d)))
    {u v : Site d} (htu : t ≠ u) (htv : t ≠ v) (h : IsOpenEdge d ω u v) :
    IsOpenEdge d (removeSite t ω) u v := by
  obtain ⟨hadj, hopen⟩ := h
  refine ⟨hadj, ?_⟩
  have hnotmem : t ∉ s(u, v) := by
    rw [Sym2.mem_iff]; push Not; exact ⟨htu, htv⟩
  rw [removeSite_apply_of_notMem hnotmem]; exact hopen





theorem bc46_armLink_survives (t : Site d) (ω : ConfigSpace (Sym2 (Site d)))
    {x bx : Site d} (htx : t ≠ x) (htbx : t ≠ bx) (hedge : IsOpenEdge d ω x bx) :
    Connected d (removeSite t ω) x bx :=
  (bc46_openEdge_removeSite_of_ne t ω htx htbx hedge).connected


























def bc46_ArmFunnelGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ t s, t ∈ box d n → IsTrifurcation d ω t → bc37_ArmAdjacent ω n t s →
      (¬ Connected d (removeSite t ω) (b t) (b s)) ∧
      (¬ Connected d (removeSite t ω) (b t) s) ∧
      (∀ x, x ≠ t → Connected d (removeSite t ω) x s →
        Connected d (removeSite t ω) x (b x)))





theorem bc46_armCutGeometryFixed'_of_armFunnelGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc46_ArmFunnelGeometry ω n) : bc40_ArmCutGeometryFixed' ω n := by
  obtain ⟨b, hdata, hclauses⟩ := hgeo
  refine ⟨b, hdata, ?_⟩
  intro t s htbox htri hadj
  obtain ⟨hloc, hself, hlink⟩ := hclauses t s htbox htri hadj
  refine ⟨hloc, hself, ?_⟩
  intro x hxt hxs
  
  exact (hlink x hxt hxs).symm.trans hxs



























def bc46_NeighborArmFunnel (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, ¬ (x ∈ box d n ∧ IsTrifurcation d ω x) → b x = x) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ IsOpenEdge d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ t s, t ∈ box d n → IsTrifurcation d ω t → bc37_ArmAdjacent ω n t s →
      (¬ Connected d (removeSite t ω) (b t) (b s)) ∧
      (¬ Connected d (removeSite t ω) (b t) s) ∧
      (∀ x, x ∈ box d n → IsTrifurcation d ω x → x ≠ t →
        Connected d (removeSite t ω) x s → b x ≠ t))












theorem bc46_armFunnelGeometry_of_neighborArmFunnel (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc46_NeighborArmFunnel ω n) : bc46_ArmFunnelGeometry ω n := by
  obtain ⟨b, hid, hdata, hclauses⟩ := hgeo
  refine ⟨b, ?_, ?_⟩
  · 
    intro x hxbox htri
    obtain ⟨hbox, hedge, hinf⟩ := hdata x hxbox htri
    exact ⟨hbox, hedge.connected, hinf⟩
  · intro t s htbox htri hadj
    obtain ⟨hloc, hself, hmiss⟩ := hclauses t s htbox htri hadj
    refine ⟨hloc, hself, ?_⟩
    intro x hxt hxs
    by_cases hxtri : x ∈ box d n ∧ IsTrifurcation d ω x
    · 
      obtain ⟨_, hedge, _⟩ := hdata x hxtri.1 hxtri.2
      have hbxt : b x ≠ t := hmiss x hxtri.1 hxtri.2 hxt hxs
      exact bc46_armLink_survives t ω (Ne.symm hxt) (Ne.symm hbxt) hedge
    · 
      rw [hid x hxtri]



theorem bc46_parentFunneling_of_armFunnelGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc46_ArmFunnelGeometry ω n) : bc37_ParentFunneling ω n :=
  bc45_parentFunneling_of_cutGeometryFixed' ω n
    (bc46_armCutGeometryFixed'_of_armFunnelGeometry ω n hgeo)


theorem bc46_selfDownArm_of_armFunnelGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc46_ArmFunnelGeometry ω n) : bc36_SelfDownArm ω n :=
  bc45_selfDownArm_of_cutGeometryFixed' ω n
    (bc46_armCutGeometryFixed'_of_armFunnelGeometry ω n hgeo)







theorem bc46_burton_keane_bernoulli_of_armFunnelGeometry (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hgeo : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc46_ArmFunnelGeometry ω n)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc45_burton_keane_bernoulli hd p hp1 hp0
    (fun ω n hn => bc46_armCutGeometryFixed'_of_armFunnelGeometry ω n (hgeo ω n hn)) htrif







theorem bc46_burton_keane_bernoulli_of_neighborArmFunnel (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hgeo : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc46_NeighborArmFunnel ω n)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc46_burton_keane_bernoulli_of_armFunnelGeometry hd p hp1 hp0
    (fun ω n hn => bc46_armFunnelGeometry_of_neighborArmFunnel ω n (hgeo ω n hn)) htrif






























def bc46_CorrectedParentGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, ¬ (x ∈ box d n ∧ IsTrifurcation d ω x) → b x = x) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ IsOpenEdge d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → bc45_armDepthRank ω n x < bc45_armDepthRank ω n y →
      (¬ Connected d (removeSite y ω) (b y) (b (bc45_armForestPar ω n y))) ∧
      (¬ Connected d (removeSite y ω) (b y) (bc45_armForestPar ω n y)) ∧
      (x ≠ bc45_armForestPar ω n y → b x ≠ y))






theorem bc46_parentFunneling_of_correctedParentGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc46_CorrectedParentGeometry ω n) : bc37_ParentFunneling ω n := by
  obtain ⟨b, hid, hdata, hclauses⟩ := hgeo
  
  have hdataC : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite := by
    intro x hxbox htri
    obtain ⟨hbox, hedge, hinf⟩ := hdata x hxbox htri
    exact ⟨hbox, hedge.connected, hinf⟩
  refine ⟨b, bc45_armDepthRank ω n, bc45_armForestPar ω n, hdataC,
    bc45_armDepthRank_injective ω n, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hparT, hpadj, hprank⟩ :=
    bc45_rooting_spec ω n x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hloc, hself, hmiss⟩ := hclauses x hxbox htri y hybox htriy hxy hconn hlt
  refine ⟨hloc, hself, fun hxne => ?_⟩
  
  have hxT : x ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
  have hyT : y ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
  
  have hrs : Connected d (removeSite y ω) x (bc45_armForestPar ω n y) :=
    bc45_rootWard_connected ω n hxT hyT hxy hconn hlt hpadj hparT hprank
  
  have hbxy : b x ≠ y := hmiss hxne
  obtain ⟨_, hedge, _⟩ := hdata x hxbox htri
  have hlink : Connected d (removeSite y ω) x (b x) :=
    bc46_armLink_survives y ω (Ne.symm hxy) (Ne.symm hbxy) hedge
  
  exact hlink.symm.trans hrs


theorem bc46_selfDownArm_of_correctedParentGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : bc46_CorrectedParentGeometry ω n) : bc36_SelfDownArm ω n :=
  bc37_selfDownArm_of_parentFunneling ω n
    (bc46_parentFunneling_of_correctedParentGeometry ω n hgeo)







theorem bc46_burton_keane_bernoulli_of_correctedParentGeometry (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hgeo : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      bc46_CorrectedParentGeometry ω n)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc36_burton_keane_bernoulli_of_selfDownArm hd p hp1 hp0
    (fun ω n hn => bc46_selfDownArm_of_correctedParentGeometry ω n (hgeo ω n hn)) htrif




theorem bc46_correctedParentGeometry_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc46_CorrectedParentGeometry ω n := by
  refine ⟨id, fun _ _ => rfl, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)















































def bc46_clawLab (c v : Fin 10) : Fin 10 :=
  if c = 0 then      
    (if v = 0 then 0
     else if v = 1 ∨ v = 4 ∨ v = 5 then 1
     else if v = 2 ∨ v = 6 ∨ v = 7 then 2 else 3)
  else if c = 1 then 
    (if v = 1 then 1 else if v = 4 then 4 else if v = 5 then 5 else 0)
  else if c = 2 then 
    (if v = 2 then 2 else if v = 6 then 6 else if v = 7 then 7 else 0)
  else               
    (if v = 3 then 3 else if v = 8 then 8 else if v = 9 then 9 else 0)




def bc46_clawB : Fin 10 → Fin 10 := ![5, 4, 6, 8, 4, 5, 6, 7, 8, 9]








theorem bc46_clawShadow_hubCut_fails :
    ¬ ((bc46_clawLab 0 (bc46_clawB 0) ≠ bc46_clawLab 0 (bc46_clawB 1)) ∧   
       (bc46_clawLab 0 (bc46_clawB 0) ≠ bc46_clawLab 0 1)) := by            
  intro ⟨hloc, _hself⟩; exact hloc (by decide)








theorem bc46_clawShadow_funnelAtParent_fails :
    (0 : Fin 10) ≠ 1 ∧                                    
    bc46_clawLab 1 0 = bc46_clawLab 1 0 ∧                 
    bc46_clawLab 1 (bc46_clawB 0) ≠ bc46_clawLab 1 0 := by 
  refine ⟨by decide, rfl, by decide⟩







theorem bc46_clawShadow_pipeline_clauses_ok :
    (bc46_clawLab 1 (bc46_clawB 1) ≠ bc46_clawLab 1 (bc46_clawB 0)) ∧   
    (bc46_clawLab 1 (bc46_clawB 1) ≠ bc46_clawLab 1 0) ∧                
    
    (∀ x : Fin 10, x ≠ 1 → x ≠ 0 → bc46_clawLab 1 x = bc46_clawLab 1 0 →
      bc46_clawLab 1 (bc46_clawB x) = bc46_clawLab 1 0) := by
  refine ⟨by decide, by decide, by decide⟩






theorem bc46_clawShadow_guard_nontrivial :
    (bc46_clawLab 1 2 = bc46_clawLab 1 0 ∧ bc46_clawLab 1 3 = bc46_clawLab 1 0) ∧
    (bc46_clawLab 1 4 ≠ bc46_clawLab 1 0 ∧ bc46_clawLab 1 5 ≠ bc46_clawLab 1 0) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩


















theorem bc46_clawShadow_correctedParentGeometry_ok :
    
    (∀ y : Fin 10, (y = 1 ∨ y = 2 ∨ y = 3) →
      (bc46_clawLab y (bc46_clawB y) ≠ bc46_clawLab y (bc46_clawB 0)) ∧   
      (bc46_clawLab y (bc46_clawB y) ≠ bc46_clawLab y 0)) ∧               
    
    
    (∀ y : Fin 10, (y = 1 ∨ y = 2 ∨ y = 3) →
      ∀ x : Fin 10, x ≠ y → x ≠ 0 → bc46_clawLab y x = bc46_clawLab y 0 →
        bc46_clawLab y (bc46_clawB x) = bc46_clawLab y 0) := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

















def bc46_chainLab (c v : Fin 8) : Fin 8 :=
  if c = 0 then      
    (if v = 0 then 0 else if v = 4 then 4 else 1)
  else if c = 1 then 
    (if v = 1 then 1 else if v = 5 then 5 else if v = 0 ∨ v = 4 then 0 else 2)
  else if c = 2 then 
    (if v = 2 then 2 else if v = 6 then 6 else if v = 3 ∨ v = 7 then 3 else 0)
  else               
    (if v = 3 then 3 else if v = 7 then 7 else 0)


def bc46_chainB : Fin 8 → Fin 8 := ![4, 5, 6, 7, 4, 5, 6, 7]







theorem bc46_chainShadow_all_clauses_hold :
    ∀ t s : Fin 8, (t = 0 ∧ s = 1) ∨ (t = 1 ∧ s = 0) ∨ (t = 1 ∧ s = 2) ∨
        (t = 2 ∧ s = 1) ∨ (t = 2 ∧ s = 3) ∨ (t = 3 ∧ s = 2) →
      (bc46_chainLab t (bc46_chainB t) ≠ bc46_chainLab t (bc46_chainB s)) ∧   
      (bc46_chainLab t (bc46_chainB t) ≠ bc46_chainLab t s) ∧                 
      (∀ x : Fin 8, x ≠ t → bc46_chainLab t x = bc46_chainLab t s →           
        bc46_chainLab t (bc46_chainB x) = bc46_chainLab t s) := by
  decide





theorem bc46_chainShadow_guard_nontrivial :
    (bc46_chainLab 2 0 = bc46_chainLab 2 1 ∧ bc46_chainLab 2 5 = bc46_chainLab 2 1) ∧
    (bc46_chainLab 2 3 ≠ bc46_chainLab 2 1 ∧ bc46_chainLab 2 7 ≠ bc46_chainLab 2 1) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩

end StatMech.Walls
