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
import Code.Percolation.BurtonKeaneMerge
import Code.Percolation.TrifurcationCount
import Code.Percolation.BurtonKeaneClose2
import Code.Percolation.DisjointArmEndsClose
import Code.Percolation.DisjointArmEndsProve
import Code.Percolation.DisjointArmEndsProve2
import Code.Percolation.DisjointArmEndsFinal
import Code.Percolation.PrivateArmProve
import Code.Percolation.BKForestLib

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}













theorem fsp_singleCut_sep_of_distinctWitness (ω : ConfigSpace (Sym2 (Site d)))
    {x a c bx by_ : Site d}
    (hdis : ¬ Connected d (removeSite x ω) a c)
    (hbx : bkfl_inArm ω x a bx) (hby : bkfl_inArm ω x c by_) :
    ¬ Connected d (removeSite x ω) bx by_ :=
  bkfl_arms_separate ω hdis hbx hby




















def fsp_TreeSelector (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y →
      ¬ Connected d (removeSite x ω) (b x) (b y))





theorem fsp_treeSelector_iff_singleCut (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    fsp_TreeSelector ω n ↔ daep2_SingleCutBranchSeparation ω n := Iff.rfl


theorem fsp_singleCut_of_treeSelector (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : fsp_TreeSelector ω n) : daep2_SingleCutBranchSeparation ω n := h













def fsp_ArmPlacement (ω : ConfigSpace (Sym2 (Site d))) (b : Site d → Site d) (x y : Site d) :
    Prop :=
  ∃ a c : Site d, ¬ Connected d (removeSite x ω) a c ∧
    bkfl_inArm ω x a (b x) ∧ bkfl_inArm ω x c (b y)



theorem fsp_singleCutSep_of_armPlacement (ω : ConfigSpace (Sym2 (Site d)))
    (b : Site d → Site d) {x y : Site d} (h : fsp_ArmPlacement ω b x y) :
    ¬ Connected d (removeSite x ω) (b x) (b y) := by
  obtain ⟨a, c, hdis, hbx, hby⟩ := h
  exact fsp_singleCut_sep_of_distinctWitness ω hdis hbx hby





















def fsp_RootedArmOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → fsp_ArmPlacement ω b x y)




theorem fsp_treeSelector_of_rootedArmOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : fsp_RootedArmOrder ω n) : fsp_TreeSelector ω n := by
  obtain ⟨b, hdata, hplace⟩ := h
  refine ⟨b, hdata, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn
  exact fsp_singleCutSep_of_armPlacement ω b (hplace x hxbox htri y hybox htriy hxy hconn)


theorem fsp_singleCut_of_rootedArmOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : fsp_RootedArmOrder ω n) : daep2_SingleCutBranchSeparation ω n :=
  fsp_singleCut_of_treeSelector ω n (fsp_treeSelector_of_rootedArmOrder ω n h)















theorem fsp_inSomeArm_of_connected (ω : ConfigSpace (Sym2 (Site d))) {x v : Site d}
    (hxv : Connected d ω x v) (hne : x ≠ v) :
    ∃ a, (openSubgraph d ω).Adj x a ∧ Connected d (removeSite x ω) a v := by
  obtain ⟨p, hp⟩ := hxv.exists_isPath
  cases p with
  | nil => exact absurd rfl hne
  | @cons _ a _ hadj q =>
    refine ⟨a, hadj, ?_⟩
    
    have hnodup := hp.support_nodup
    rw [Walk.support_cons] at hnodup
    have hxq : x ∉ q.support := (List.nodup_cons.mp hnodup).1
    exact pap_connected_removeSite_of_walk_avoid ω x q hxq









open Classical in



noncomputable def fsp_armWitness (ω : ConfigSpace (Sym2 (Site d))) (x v : Site d) : Site d :=
  if h : Connected d ω x v ∧ x ≠ v then
    (fsp_inSomeArm_of_connected ω h.1 h.2).choose
  else x



theorem fsp_armWitness_inArm (ω : ConfigSpace (Sym2 (Site d))) {x v : Site d}
    (hxv : Connected d ω x v) (hne : x ≠ v) :
    Connected d (removeSite x ω) (fsp_armWitness ω x v) v := by
  classical
  rw [fsp_armWitness, dif_pos ⟨hxv, hne⟩]
  exact (fsp_inSomeArm_of_connected ω hxv hne).choose_spec.2


theorem fsp_armWitness_adj (ω : ConfigSpace (Sym2 (Site d))) {x v : Site d}
    (hxv : Connected d ω x v) (hne : x ≠ v) :
    (openSubgraph d ω).Adj x (fsp_armWitness ω x v) := by
  classical
  rw [fsp_armWitness, dif_pos ⟨hxv, hne⟩]
  exact (fsp_inSomeArm_of_connected ω hxv hne).choose_spec.1



def fsp_sameArm (ω : ConfigSpace (Sym2 (Site d))) (x u v : Site d) : Prop :=
  Connected d (removeSite x ω) (fsp_armWitness ω x u) (fsp_armWitness ω x v)





theorem fsp_sep_of_notSameArm (ω : ConfigSpace (Sym2 (Site d))) {x u v : Site d}
    (hxu : Connected d ω x u) (hneu : x ≠ u)
    (hxv : Connected d ω x v) (hnev : x ≠ v)
    (hdiv : ¬ fsp_sameArm ω x u v) :
    ¬ Connected d (removeSite x ω) u v := by
  intro huv
  
  exact hdiv ((fsp_armWitness_inArm ω hxu hneu).trans
    (huv.trans (fsp_armWitness_inArm ω hxv hnev).symm))












theorem fsp_armPlacement_of_divergentWitness (ω : ConfigSpace (Sym2 (Site d)))
    (b : Site d → Site d) {x y a c : Site d}
    (hdis : ¬ Connected d (removeSite x ω) a c)
    (hbx : bkfl_inArm ω x a (b x)) (hby : bkfl_inArm ω x c (b y)) :
    fsp_ArmPlacement ω b x y := ⟨a, c, hdis, hbx, hby⟩



theorem fsp_inArm_of_witness (ω : ConfigSpace (Sym2 (Site d))) {x a v : Site d}
    (h : Connected d (removeSite x ω) a v) : bkfl_inArm ω x a v := h



theorem fsp_inArm_self (ω : ConfigSpace (Sym2 (Site d))) (x a : Site d) :
    bkfl_inArm ω x a a := bkfl_inArm_self ω x a
























def fsp_DivergentArmOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ b x ≠ x ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → ¬ fsp_sameArm ω x (b x) (b y))






theorem fsp_armPlacement_of_divergence (ω : ConfigSpace (Sym2 (Site d)))
    (b : Site d → Site d) {x y : Site d}
    (hbxx : b x ≠ x) (hbyx : x ≠ b y)
    (hxbx : Connected d ω x (b x)) (hxby : Connected d ω x (b y))
    (hdiv : ¬ fsp_sameArm ω x (b x) (b y)) :
    fsp_ArmPlacement ω b x y := by
  refine ⟨fsp_armWitness ω x (b x), fsp_armWitness ω x (b y), hdiv, ?_, ?_⟩
  · exact fsp_armWitness_inArm ω hxbx (Ne.symm hbxx)
  · exact fsp_armWitness_inArm ω hxby hbyx







theorem fsp_rootedArmOrder_of_divergentArmOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : fsp_DivergentArmOrder ω n) : fsp_RootedArmOrder ω n := by
  obtain ⟨b, hdata, hdiv⟩ := h
  refine ⟨b, ?_, ?_⟩
  · intro x hxbox htri
    obtain ⟨hbox, _, hconn, hinf⟩ := hdata x hxbox htri
    exact ⟨hbox, hconn, hinf⟩
  · intro x hxbox htri y hybox htriy hxy hconn
    obtain ⟨_, hbxx, hxbx, _⟩ := hdata x hxbox htri
    obtain ⟨_, hbyy, hyby, _⟩ := hdata y hybox htriy
    
    have hxby : Connected d ω x (b y) := hconn.trans hyby
    
    
    
    
    by_cases hcase : x = b y
    · 
      
      
      
      
      refine ⟨fsp_armWitness ω x (b x), fsp_armWitness ω x (b y),
        hdiv x hxbox htri y hybox htriy hxy hconn, ?_, ?_⟩
      · exact fsp_armWitness_inArm ω hxbx (Ne.symm hbxx)
      · 
        
        have hwit : fsp_armWitness ω x (b y) = x := by
          rw [← hcase]; simp only [fsp_armWitness]
          rw [dif_neg (by rintro ⟨_, hne⟩; exact hne rfl)]
        show Connected d (removeSite x ω) (fsp_armWitness ω x (b y)) (b y)
        rw [hwit, ← hcase]
    · exact fsp_armPlacement_of_divergence ω b hbxx hcase hxbx hxby
        (hdiv x hxbox htri y hybox htriy hxy hconn)










theorem fsp_rootedArmOrder_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    fsp_RootedArmOrder ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)






theorem fsp_rootedArmOrder_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    fsp_RootedArmOrder ω n := by
  classical
  have hT : tfc_trifFinset ω n = {x₀} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨tfc_mem_trifFinset.mpr ⟨hx0box, htri0⟩, ?_⟩
    intro y hy; rw [tfc_mem_trifFinset] at hy; exact huniq y hy.1 hy.2
  have hcut : removeSites (tfc_trifFinset ω n) ω = removeSite x₀ ω := by
    rw [hT, daep_removeSites_singleton]
  refine ⟨fun _ => a, ?_, ?_⟩
  · intro x hxbox htri
    have hx0 : x = x₀ := huniq x hxbox htri
    subst hx0
    refine ⟨habox, haconn, ?_⟩
    rw [hcut]; exact hainf
  · intro x hxbox htri y hybox htriy hxy _
    exact absurd ((huniq x hxbox htri).trans (huniq y hybox htriy).symm) hxy














theorem fsp_rootedArmOrder_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d)
    (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hdata_x : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hdata_y : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hplace_xy : fsp_ArmPlacement ω b x₀ y₀)
    (hplace_yx : fsp_ArmPlacement ω b y₀ x₀) :
    fsp_RootedArmOrder ω n := by
  classical
  refine ⟨b, ?_, ?_⟩
  · intro x hxbox htri
    rcases htwo x hxbox htri with rfl | rfl
    · exact hdata_x
    · exact hdata_y
  · intro x hxbox htri y hybox htriy hxy _
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo y hybox htriy with rfl | rfl
      · exact absurd rfl hxy
      · exact hplace_xy
    · rcases htwo y hybox htriy with rfl | rfl
      · exact hplace_yx
      · exact absurd rfl hxy







theorem fsp_divergentArmOrder_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d)
    (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hdata_x : b x₀ ∈ box d n ∧ b x₀ ≠ x₀ ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hdata_y : b y₀ ∈ box d n ∧ b y₀ ≠ y₀ ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hdiv_xy : ¬ fsp_sameArm ω x₀ (b x₀) (b y₀))
    (hdiv_yx : ¬ fsp_sameArm ω y₀ (b y₀) (b x₀)) :
    fsp_DivergentArmOrder ω n := by
  classical
  refine ⟨b, ?_, ?_⟩
  · intro x hxbox htri
    rcases htwo x hxbox htri with rfl | rfl
    · exact hdata_x
    · exact hdata_y
  · intro x hxbox htri y hybox htriy hxy _
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo y hybox htriy with rfl | rfl
      · exact absurd rfl hxy
      · exact hdiv_xy
    · rcases htwo y hybox htriy with rfl | rfl
      · exact hdiv_yx
      · exact absurd rfl hxy










theorem fsp_Tcount_le_boundary_of_treeSelector (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : fsp_TreeSelector ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  daep2_Tcount_le_boundary_of_singleCut ω n hn (fsp_singleCut_of_treeSelector ω n h)


theorem fsp_Tcount_le_boundary_of_rootedArmOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : fsp_RootedArmOrder ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  fsp_Tcount_le_boundary_of_treeSelector ω n hn (fsp_treeSelector_of_rootedArmOrder ω n h)














theorem fsp_burton_keane_bernoulli_of_treeSelector (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fsp_TreeSelector ω n)
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
  daep2_burton_keane_bernoulli_of_singleCut hd p hp1 hp0
    (fun ω n hn => fsp_singleCut_of_treeSelector ω n (hres ω n hn))
    htrif




theorem fsp_burton_keane_bernoulli_of_rootedArmOrder (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fsp_RootedArmOrder ω n)
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
  fsp_burton_keane_bernoulli_of_treeSelector hd p hp1 hp0
    (fun ω n hn => fsp_treeSelector_of_rootedArmOrder ω n (hres ω n hn))
    htrif


theorem fsp_Tcount_le_boundary_of_divergentArmOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : fsp_DivergentArmOrder ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  fsp_Tcount_le_boundary_of_rootedArmOrder ω n hn
    (fsp_rootedArmOrder_of_divergentArmOrder ω n h)




theorem fsp_burton_keane_bernoulli_of_divergentArmOrder (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fsp_DivergentArmOrder ω n)
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
  fsp_burton_keane_bernoulli_of_rootedArmOrder hd p hp1 hp0
    (fun ω n hn => fsp_rootedArmOrder_of_divergentArmOrder ω n (hres ω n hn))
    htrif

end Percolation

end StatMech
