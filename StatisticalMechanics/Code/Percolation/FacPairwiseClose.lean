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

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}



























def fpc_DirectionalChosenArmDivergence (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y →
      ¬ fsp_sameArm ω x (b x) (b y) ∨ ¬ fsp_sameArm ω y (b x) (b y))


















theorem fpc_pairwiseCutSeparation_of_directionalDivergence (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : fpc_DirectionalChosenArmDivergence ω n) :
    fac_PairwiseCutSeparation ω n := by
  classical
  obtain ⟨b, hdata, hdiv⟩ := h
  refine ⟨b, hdata, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn
  set T := tfc_trifFinset ω n with hT
  
  have hxT : x ∈ T := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
  have hyT : y ∈ T := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
  obtain ⟨_, hxbx, hbxinf⟩ := hdata x hxbox htri
  obtain ⟨_, hyby, hbyinf⟩ := hdata y hybox htriy
  have hbxnotin : b x ∉ T := stac_infiniteCluster_notMem T ω hbxinf
  have hbynotin : b y ∉ T := stac_infiniteCluster_notMem T ω hbyinf
  
  have hne_x_bx : x ≠ b x := fun heq => hbxnotin (heq ▸ hxT)
  have hne_y_by : y ≠ b y := fun heq => hbynotin (heq ▸ hyT)
  have hne_x_by : x ≠ b y := fun heq => hbynotin (heq ▸ hxT)
  have hne_y_bx : y ≠ b x := fun heq => hbxnotin (heq ▸ hyT)
  
  have hx_bx : Connected d ω x (b x) := hxbx
  have hx_by : Connected d ω x (b y) := hconn.trans hyby
  have hy_bx : Connected d ω y (b x) := hconn.symm.trans hxbx
  have hy_by : Connected d ω y (b y) := hyby
  rcases hdiv x hxbox htri y hybox htriy hxy hconn with hdx | hdy
  · 
    exact Or.inl (fsp_sep_of_notSameArm ω hx_bx hne_x_bx hx_by hne_x_by hdx)
  · 
    exact Or.inr (fsp_sep_of_notSameArm ω hy_bx hne_y_bx hy_by hne_y_by hdy)



theorem fpc_globalForestArms_of_directionalDivergence (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : fpc_DirectionalChosenArmDivergence ω n) :
    aed_GlobalForestArms ω n :=
  fac_globalForestArms_of_pairwiseCutSeparation ω n
    (fpc_pairwiseCutSeparation_of_directionalDivergence ω n h)



















theorem fpc_directionalDivergence_of_divergentArmOrder (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : fsp_DivergentArmOrder ω n) :
    fpc_DirectionalChosenArmDivergence ω n := by
  obtain ⟨b, hdata, hdiv⟩ := h
  refine ⟨b, ?_, ?_⟩
  · 
    intro x hxbox htri
    obtain ⟨hbox, _, hconn, hinf⟩ := hdata x hxbox htri
    exact ⟨hbox, hconn, hinf⟩
  · 
    intro x hxbox htri y hybox htriy hxy hconn
    exact Or.inl (hdiv x hxbox htri y hybox htriy hxy hconn)



theorem fpc_globalForestArms_of_divergentArmOrder (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : fsp_DivergentArmOrder ω n) :
    aed_GlobalForestArms ω n :=
  fpc_globalForestArms_of_directionalDivergence ω n
    (fpc_directionalDivergence_of_divergentArmOrder ω n h)









theorem fpc_directionalDivergence_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    fpc_DirectionalChosenArmDivergence ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri _ _ _ _ _; exact absurd htri (hno x hxbox)






theorem fpc_directionalDivergence_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    fpc_DirectionalChosenArmDivergence ω n := by
  classical
  
  obtain ⟨b, hdata, _⟩ := daepf_privateArm_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq
  refine ⟨b, hdata, ?_⟩
  intro x hxbox htri y hybox htriy hxy _hconn
  exact absurd ((huniq x hxbox htri).trans (huniq y hybox htriy).symm) hxy







theorem fpc_directionalDivergence_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d) (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hdiv_x : ¬ fsp_sameArm ω x₀ (b x₀) (b y₀))
    (hdiv_y : ¬ fsp_sameArm ω y₀ (b y₀) (b x₀)) :
    fpc_DirectionalChosenArmDivergence ω n := by
  classical
  refine ⟨b, ?_, ?_⟩
  · 
    intro x hxbox htri
    rcases htwo x hxbox htri with rfl | rfl
    · exact hbx0
    · exact hby0
  · 
    intro x hxbox htri y hybox htriy hxy _hconn
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo y hybox htriy with rfl | rfl
      · exact absurd rfl hxy
      · exact Or.inl hdiv_x
    · rcases htwo y hybox htriy with rfl | rfl
      · exact Or.inl hdiv_y
      · exact absurd rfl hxy
































theorem fpc_directionalDivergence_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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
    fpc_DirectionalChosenArmDivergence ω n := by
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
  
  refine ⟨b, hbdata, ?_⟩
  intro x hxbox htri x' hx'box htri' hxx' _hconn
  rcases hsingle x hxbox htri with hxx0 | ⟨i, rfl⟩
  · 
    rw [hxx0]
    rcases hsingle x' hx'box htri' with hx'0 | ⟨i, rfl⟩
    · 
      exact absurd (hxx0.trans hx'0.symm) hxx'
    · 
      by_cases hji : (j₀ : Fin 3) = i
      · 
        subst hji
        refine Or.inr ?_
        intro hsame
        exact hcentral
          ((hlyf j₀ (b x₀) (b (y j₀)) (hyi_bx0 j₀) (hne_yi_bx0 j₀)
            (hyi_byi j₀) (hne_yi_byj j₀ j₀)).mpr hsame)
      · 
        refine Or.inl ?_
        have hcollx : lx (b x₀) ≠ lx (b (y i)) := by rw [hcx, hcy i]; exact hji
        intro hsame
        exact hcollx ((hlxf (b x₀) (b (y i)) hx0bx0 hne_bx0
          (hx0byi i) (hne_x0_byi i)).mpr hsame)
  · 
    rcases hsingle x' hx'box htri' with hx'0 | ⟨j, rfl⟩
    · 
      rw [hx'0]
      by_cases hji : (j₀ : Fin 3) = i
      · 
        subst hji
        refine Or.inl ?_
        intro hsame
        exact hcentral
          (((hlyf j₀ (b (y j₀)) (b x₀) (hyi_byi j₀) (hne_yi_byj j₀ j₀)
            (hyi_bx0 j₀) (hne_yi_bx0 j₀)).mpr hsame).symm)
      · 
        refine Or.inr ?_
        have hcollx : lx (b (y i)) ≠ lx (b x₀) := by
          rw [hcx, hcy i]; exact fun h => hji h.symm
        intro hsame
        exact hcollx ((hlxf (b (y i)) (b x₀) (hx0byi i) (hne_x0_byi i)
          hx0bx0 hne_bx0).mpr hsame)
    · 
      
      
      have hij : i ≠ j := fun h => hxx' (by rw [h])
      refine Or.inl ?_
      have hG_byi : ly i (b (y i)) ≠ 0 :=
        (not_iff_not.mpr (hGstar i (b (y i)) (hx0byi i) (hne_x0_byi i)
          (hyi_byi i) (hne_yi_byj i i))).mpr (by rw [not_not, hcy i])
      have hG_byj : ly i (b (y j)) = 0 :=
        (hGstar i (b (y j)) (hx0byi j) (hne_x0_byi j)
          (hyi_byj i j) (hne_yi_byj i j)).mpr (by rw [hcy j]; exact fun h => hij h.symm)
      have hcolly : ly i (b (y i)) ≠ ly i (b (y j)) := by rw [hG_byj]; exact hG_byi
      intro hsame
      exact hcolly ((hlyf i (b (y i)) (b (y j)) (hyi_byi i) (hne_yi_byj i i)
        (hyi_byj i j) (hne_yi_byj i j)).mpr hsame)











theorem fpc_Tcount_le_boundary_of_directionalDivergence (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (hn : 1 ≤ n) (h : fpc_DirectionalChosenArmDivergence ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  fac_Tcount_le_boundary_of_pairwiseCutSeparation ω n hn
    (fpc_pairwiseCutSeparation_of_directionalDivergence ω n h)


















theorem fpc_burton_keane_bernoulli_of_directionalDivergence (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      fpc_DirectionalChosenArmDivergence ω n)
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
  fac_burton_keane_bernoulli_of_pairwiseCutSeparation hd p hp1 hp0
    (fun ω n hn => fpc_pairwiseCutSeparation_of_directionalDivergence ω n (hres ω n hn))
    htrif

end Percolation

end StatMech
