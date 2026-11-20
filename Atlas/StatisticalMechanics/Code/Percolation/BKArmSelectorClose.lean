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
import Code.Percolation.BKForestLib
import Code.Percolation.BKHallSDRClose
import Code.Percolation.ArmEndDisjointClose
import Code.Percolation.ForestSelectorProve
import Code.Percolation.SpanningTreeArmClose
import Code.Percolation.ForestAcyclicityClose
import Code.Percolation.FacPairwiseClose

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}










theorem bas_sameArm_symm (ω : ConfigSpace (Sym2 (Site d))) (x u v : Site d)
    (h : fsp_sameArm ω x u v) : fsp_sameArm ω x v u :=
  Connected.symm h


























def bas_RootedTreeArmSelection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (b : Site d → Site d) (lt : Site d → Site d → Prop),
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → lt x y ∨ lt y x) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      Connected d ω x y → lt x y → ¬ fsp_sameArm ω y (b x) (b y))













theorem bas_directionalDivergence_of_rootedTreeArmSelection (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : bas_RootedTreeArmSelection ω n) :
    fpc_DirectionalChosenArmDivergence ω n := by
  obtain ⟨b, lt, hdata, hcomp, hdeep⟩ := h
  refine ⟨b, hdata, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn
  rcases hcomp x hxbox htri y hybox htriy hxy hconn with hlt | hlt
  · 
    exact Or.inr (hdeep x hxbox htri y hybox htriy hconn hlt)
  · 
    refine Or.inl ?_
    intro hsame
    exact hdeep y hybox htriy x hxbox htri hconn.symm hlt (bas_sameArm_symm ω x (b x) (b y) hsame)



theorem bas_pairwiseCutSeparation_of_rootedTreeArmSelection (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : bas_RootedTreeArmSelection ω n) :
    fac_PairwiseCutSeparation ω n :=
  fpc_pairwiseCutSeparation_of_directionalDivergence ω n
    (bas_directionalDivergence_of_rootedTreeArmSelection ω n h)



theorem bas_globalForestArms_of_rootedTreeArmSelection (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : bas_RootedTreeArmSelection ω n) :
    aed_GlobalForestArms ω n :=
  fac_globalForestArms_of_pairwiseCutSeparation ω n
    (bas_pairwiseCutSeparation_of_rootedTreeArmSelection ω n h)








theorem bas_rootedTreeArmSelection_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bas_RootedTreeArmSelection ω n := by
  refine ⟨id, (fun _ _ => False), ?_, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)






theorem bas_rootedTreeArmSelection_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    bas_RootedTreeArmSelection ω n := by
  classical
  obtain ⟨b, hdata, _⟩ := daepf_privateArm_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq
  refine ⟨b, (fun _ _ => False), hdata, ?_, ?_⟩
  · intro x hxbox htri y hybox htriy hxy _
    exact absurd ((huniq x hxbox htri).trans (huniq y hybox htriy).symm) hxy
  · intro x hxbox htri y hybox htriy _ hlt
    exact absurd hlt id






theorem bas_rootedTreeArmSelection_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d) (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hdeep : ¬ fsp_sameArm ω y₀ (b x₀) (b y₀)) :
    bas_RootedTreeArmSelection ω n := by
  classical
  
  refine ⟨b, (fun u v => u = x₀ ∧ v = y₀), ?_, ?_, ?_⟩
  · 
    intro x hxbox htri
    rcases htwo x hxbox htri with rfl | rfl
    · exact hbx0
    · exact hby0
  · 
    intro x hxbox htri y hybox htriy hxy _
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo y hybox htriy with rfl | rfl
      · exact absurd rfl hxy
      · exact Or.inl ⟨rfl, rfl⟩
    · rcases htwo y hybox htriy with rfl | rfl
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd rfl hxy
  · 
    intro x hxbox htri y hybox htriy _ hlt
    obtain ⟨rfl, rfl⟩ := hlt
    exact hdeep






























theorem bas_rootedTreeArmSelection_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d) (y : Fin 3 → Site d) (lx : Site d → Fin 3) (ly : Fin 3 → Site d → Fin 3)
    (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i ∧
      Connected d ω x₀ (y i))
    (_hyinj : Function.Injective y)
    (hlxf : ∀ u v, Connected d ω x₀ u → x₀ ≠ u → Connected d ω x₀ v → x₀ ≠ v →
      (lx u = lx v ↔ fsp_sameArm ω x₀ u v))
    (hlyf : ∀ i u v, Connected d ω (y i) u → y i ≠ u → Connected d ω (y i) v → y i ≠ v →
      (ly i u = ly i v ↔ fsp_sameArm ω (y i) u v))
    (hGstar : ∀ i w, Connected d ω x₀ w → x₀ ≠ w → Connected d ω (y i) w → y i ≠ w →
      (ly i w = 0 ↔ lx w ≠ i))
    (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
    (b : Site d → Site d)
    (hbdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
    (hcy : ∀ i, lx (b (y i)) = i)
    {j₀ : Fin 3} (hcx : lx (b x₀) = j₀)
    (hcentral : ly j₀ (b x₀) ≠ ly j₀ (b (y j₀))) :
    bas_RootedTreeArmSelection ω n := by
  classical
  set T := tfc_trifFinset ω n with hT
  
  have hx0T : x₀ ∈ T := tfc_mem_trifFinset.mpr ⟨hx0box, htri0⟩
  have hyT : ∀ i, y i ∈ T := fun i =>
    tfc_mem_trifFinset.mpr ⟨(hydata i).1, (hydata i).2.1⟩
  
  have hbx0notin : b x₀ ∉ T :=
    stac_infiniteCluster_notMem T ω (hbdata x₀ hx0box htri0).2.2
  have hbynotin : ∀ i, b (y i) ∉ T := fun i =>
    stac_infiniteCluster_notMem T ω (hbdata (y i) (hydata i).1 (hydata i).2.1).2.2
  
  have hne_bx0 : x₀ ≠ b x₀ := fun h => hbx0notin (h ▸ hx0T)
  have hne_x0_byi : ∀ i, x₀ ≠ b (y i) := fun i h => hbynotin i (h ▸ hx0T)
  have hne_yi_byj : ∀ i j, y i ≠ b (y j) := fun i j h => hbynotin j (h ▸ hyT i)
  have hne_yi_bx0 : ∀ i, y i ≠ b x₀ := fun i h => hbx0notin (h ▸ hyT i)
  
  have hx0byi : ∀ i, Connected d ω x₀ (b (y i)) := fun i =>
    (hydata i).2.2.2.trans (hbdata (y i) (hydata i).1 (hydata i).2.1).2.1
  have hyi_byi : ∀ i, Connected d ω (y i) (b (y i)) := fun i =>
    (hbdata (y i) (hydata i).1 (hydata i).2.1).2.1
  have hyi_byj : ∀ i j, Connected d ω (y i) (b (y j)) := fun i j =>
    (hydata i).2.2.2.symm.trans (hx0byi j)
  have hx0bx0 : Connected d ω x₀ (b x₀) := (hbdata x₀ hx0box htri0).2.1
  have hyi_bx0 : ∀ i, Connected d ω (y i) (b x₀) := fun i =>
    (hydata i).2.2.2.symm.trans hx0bx0
  
  refine ⟨b, (fun u v =>
      (u = x₀ ∧ ∃ i, v = y i) ∨ (∃ i j, u = y i ∧ v = y j ∧ (i : ℕ) < j)),
    hbdata, ?_, ?_⟩
  · 
    intro x hxbox htri x' hx'box htri' hxx' _hconn
    rcases hsingle x hxbox htri with rfl | ⟨i, rfl⟩
    · 
      rcases hsingle x' hx'box htri' with rfl | ⟨i, rfl⟩
      · exact absurd rfl hxx'
      · exact Or.inl (Or.inl ⟨rfl, i, rfl⟩)
    · 
      rcases hsingle x' hx'box htri' with rfl | ⟨j, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, i, rfl⟩)
      · 
        have hij : i ≠ j := fun h => hxx' (by rw [h])
        rcases lt_or_gt_of_ne (a := (i : ℕ)) (b := (j : ℕ))
            (fun h => hij (Fin.ext h)) with hlt | hlt
        · exact Or.inl (Or.inr ⟨i, j, rfl, rfl, hlt⟩)
        · exact Or.inr (Or.inr ⟨j, i, rfl, rfl, hlt⟩)
  · 
    intro x hxbox htri x' hx'box htri' _hconn hlt
    rcases hlt with ⟨hxe, i, hx'e⟩ | ⟨i, j, hxe, hx'e, hij⟩
    · 
      rw [hxe, hx'e]
      by_cases hji : (j₀ : Fin 3) = i
      · 
        subst hji
        intro hsame
        exact hcentral
          ((hlyf j₀ (b x₀) (b (y j₀)) (hyi_bx0 j₀) (hne_yi_bx0 j₀)
            (hyi_byi j₀) (hne_yi_byj j₀ j₀)).mpr hsame)
      · 
        intro hsame
        
        have hG_bx0 : ly i (b x₀) = 0 :=
          (hGstar i (b x₀) hx0bx0 hne_bx0 (hyi_bx0 i) (hne_yi_bx0 i)).mpr
            (by rw [hcx]; exact hji)
        
        have hG_byi : ly i (b (y i)) ≠ 0 :=
          (not_iff_not.mpr (hGstar i (b (y i)) (hx0byi i) (hne_x0_byi i)
            (hyi_byi i) (hne_yi_byj i i))).mpr (by rw [not_not, hcy i])
        have hcolly : ly i (b x₀) ≠ ly i (b (y i)) := by rw [hG_bx0]; exact fun h => hG_byi h.symm
        exact hcolly ((hlyf i (b x₀) (b (y i)) (hyi_bx0 i) (hne_yi_bx0 i)
          (hyi_byi i) (hne_yi_byj i i)).mpr hsame)
    · 
      rw [hxe, hx'e]
      have hij' : i ≠ j := fun h => (by rw [h] at hij; exact lt_irrefl _ hij)
      intro hsame
      
      
      have hG_byi : ly j (b (y i)) = 0 :=
        (hGstar j (b (y i)) (hx0byi i) (hne_x0_byi i)
          (hyi_byj j i) (hne_yi_byj j i)).mpr (by rw [hcy i]; exact hij')
      
      have hG_byj : ly j (b (y j)) ≠ 0 :=
        (not_iff_not.mpr (hGstar j (b (y j)) (hx0byi j) (hne_x0_byi j)
          (hyi_byi j) (hne_yi_byj j j))).mpr (by rw [not_not, hcy j])
      have hcolly : ly j (b (y i)) ≠ ly j (b (y j)) := by rw [hG_byi]; exact fun h => hG_byj h.symm
      exact hcolly ((hlyf j (b (y i)) (b (y j)) (hyi_byj j i) (hne_yi_byj j i)
        (hyi_byi j) (hne_yi_byj j j)).mpr hsame)











theorem bas_Tcount_le_boundary_of_rootedTreeArmSelection (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (hn : 1 ≤ n) (h : bas_RootedTreeArmSelection ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  fpc_Tcount_le_boundary_of_directionalDivergence ω n hn
    (bas_directionalDivergence_of_rootedTreeArmSelection ω n h)

















theorem bas_burton_keane_bernoulli_of_rootedTreeArmSelection (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      bas_RootedTreeArmSelection ω n)
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
  fpc_burton_keane_bernoulli_of_directionalDivergence hd p hp1 hp0
    (fun ω n hn => bas_directionalDivergence_of_rootedTreeArmSelection ω n (hres ω n hn))
    htrif

end Percolation

end StatMech
