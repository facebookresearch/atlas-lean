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

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}














theorem fac_singleCut_of_globalCut (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    {z u v : Site d} (hzT : z ∈ T) (h : Connected d (removeSites T ω) u v) :
    Connected d (removeSite z ω) u v :=
  connected_mono (daep2_removeSites_le_removeSite T ω hzT) h





theorem fac_globalDisc_of_singleDisc (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    {z u v : Site d} (hzT : z ∈ T) (h : ¬ Connected d (removeSite z ω) u v) :
    ¬ Connected d (removeSites T ω) u v :=
  fun hc => h (fac_singleCut_of_globalCut T ω hzT hc)




theorem fac_trif_mem_finset (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) {x : Site d}
    (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x) :
    x ∈ tfc_trifFinset ω n :=
  tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩






theorem fac_globalSep_of_eitherCut (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x y u v : Site d} (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x)
    (hybox : y ∈ box d n) (htriy : IsTrifurcation d ω y)
    (h : ¬ Connected d (removeSite x ω) u v ∨ ¬ Connected d (removeSite y ω) u v) :
    ¬ Connected d (removeSites (tfc_trifFinset ω n) ω) u v := by
  rcases h with hx | hy
  · exact fac_globalDisc_of_singleDisc _ ω (fac_trif_mem_finset ω n hxbox htri) hx
  · exact fac_globalDisc_of_singleDisc _ ω (fac_trif_mem_finset ω n hybox htriy) hy























def fac_PairwiseCutSeparation (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y →
      ¬ Connected d (removeSite x ω) (b x) (b y) ∨
        ¬ Connected d (removeSite y ω) (b x) (b y))















theorem fac_globalForestArms_of_pairwiseCutSeparation (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : fac_PairwiseCutSeparation ω n) :
    aed_GlobalForestArms ω n := by
  classical
  obtain ⟨b, hdata, hpair⟩ := h
  refine ⟨b, hdata, ?_⟩
  intro x hxbox htri y hybox htriy hxy
  
  change ¬ Connected d (removeSites (tfc_trifFinset ω n) ω) (b x) (b y)
  by_cases hconn : Connected d ω x y
  · 
    exact fac_globalSep_of_eitherCut ω n hxbox htri hybox htriy
      (hpair x hxbox htri y hybox htriy hxy hconn)
  · 
    have hxa : Connected d ω x (b x) := (hdata x hxbox htri).2.1
    have hyb : Connected d ω y (b y) := (hdata y hybox htriy).2.1
    exact daep2_crossCluster_branches_globalCut_disconnected (tfc_trifFinset ω n) ω
      hxa hyb hconn

















theorem fac_pairwiseCutSeparation_of_privateArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : daepf_PrivateArm ω n) :
    fac_PairwiseCutSeparation ω n := by
  obtain ⟨b, hdata, hpair⟩ := h
  refine ⟨b, hdata, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn
  obtain ⟨hpriv, hfar⟩ := hpair x hxbox htri y hybox htriy hxy hconn
  
  refine Or.inl ?_
  intro hbxby
  exact hpriv (hbxby.trans hfar)



theorem fac_globalForestArms_of_privateArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : daepf_PrivateArm ω n) :
    aed_GlobalForestArms ω n :=
  fac_globalForestArms_of_pairwiseCutSeparation ω n
    (fac_pairwiseCutSeparation_of_privateArm ω n h)










theorem fac_pairwiseCutSeparation_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    fac_PairwiseCutSeparation ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri _ _ _ _ _; exact absurd htri (hno x hxbox)





theorem fac_pairwiseCutSeparation_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    fac_PairwiseCutSeparation ω n :=
  fac_pairwiseCutSeparation_of_privateArm ω n
    (daepf_privateArm_of_uniqueTrif ω n hx0box htri0 habox haconn hainf huniq)







theorem fac_pairwiseCutSeparation_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d) (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hsep_x : ¬ Connected d (removeSite x₀ ω) (b x₀) (b y₀))
    (hsep_y : ¬ Connected d (removeSite y₀ ω) (b y₀) (b x₀)) :
    fac_PairwiseCutSeparation ω n := by
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
      · exact Or.inl hsep_x
    · rcases htwo y hybox htriy with rfl | rfl
      · 
        exact Or.inl hsep_y
      · exact absurd rfl hxy
































theorem fac_pairwiseCutSeparation_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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
    fac_PairwiseCutSeparation ω n := by
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
        
        have hnsame : ¬ fsp_sameArm ω (y j₀) (b x₀) (b (y j₀)) := by
          intro hsame
          exact hcentral
            ((hlyf j₀ (b x₀) (b (y j₀)) (hyi_bx0 j₀) (hne_yi_bx0 j₀)
              (hyi_byi j₀) (hne_yi_byj j₀ j₀)).mpr hsame)
        exact fsp_sep_of_notSameArm ω (hyi_bx0 j₀) (hne_yi_bx0 j₀)
          (hyi_byi j₀) (hne_yi_byj j₀ j₀) hnsame
      · 
        refine Or.inl ?_
        have hcollx : lx (b x₀) ≠ lx (b (y i)) := by
          rw [hcx, hcy i]; exact hji
        have hnsame : ¬ fsp_sameArm ω x₀ (b x₀) (b (y i)) := by
          intro hsame
          exact hcollx ((hlxf (b x₀) (b (y i)) hx0bx0 hne_bx0
            (hx0byi i) (hne_x0_byi i)).mpr hsame)
        exact fsp_sep_of_notSameArm ω hx0bx0 hne_bx0 (hx0byi i) (hne_x0_byi i) hnsame
  · 
    rcases hsingle x' hx'box htri' with hx'0 | ⟨j, rfl⟩
    · 
      rw [hx'0]
      by_cases hji : (j₀ : Fin 3) = i
      · 
        subst hji
        refine Or.inl ?_
        have hnsame : ¬ fsp_sameArm ω (y j₀) (b (y j₀)) (b x₀) := by
          intro hsame
          exact hcentral
            (((hlyf j₀ (b (y j₀)) (b x₀) (hyi_byi j₀) (hne_yi_byj j₀ j₀)
              (hyi_bx0 j₀) (hne_yi_bx0 j₀)).mpr hsame).symm)
        exact fsp_sep_of_notSameArm ω (hyi_byi j₀) (hne_yi_byj j₀ j₀)
          (hyi_bx0 j₀) (hne_yi_bx0 j₀) hnsame
      · 
        refine Or.inr ?_
        have hcollx : lx (b (y i)) ≠ lx (b x₀) := by
          rw [hcx, hcy i]; exact fun h => hji h.symm
        have hnsame : ¬ fsp_sameArm ω x₀ (b (y i)) (b x₀) := by
          intro hsame
          exact hcollx ((hlxf (b (y i)) (b x₀) (hx0byi i) (hne_x0_byi i)
            hx0bx0 hne_bx0).mpr hsame)
        exact fsp_sep_of_notSameArm ω (hx0byi i) (hne_x0_byi i) hx0bx0 hne_bx0 hnsame
    · 
      
      
      have hij : i ≠ j := fun h => hxx' (by rw [h])
      refine Or.inl ?_
      
      
      
      have hG_byi : ly i (b (y i)) ≠ 0 :=
        (not_iff_not.mpr (hGstar i (b (y i)) (hx0byi i) (hne_x0_byi i)
          (hyi_byi i) (hne_yi_byj i i))).mpr (by rw [not_not, hcy i])
      have hG_byj : ly i (b (y j)) = 0 :=
        (hGstar i (b (y j)) (hx0byi j) (hne_x0_byi j)
          (hyi_byj i j) (hne_yi_byj i j)).mpr (by rw [hcy j]; exact fun h => hij h.symm)
      have hcolly : ly i (b (y i)) ≠ ly i (b (y j)) := by
        rw [hG_byj]; exact hG_byi
      have hnsame : ¬ fsp_sameArm ω (y i) (b (y i)) (b (y j)) := by
        intro hsame
        exact hcolly ((hlyf i (b (y i)) (b (y j)) (hyi_byi i) (hne_yi_byj i i)
          (hyi_byj i j) (hne_yi_byj i j)).mpr hsame)
      exact fsp_sep_of_notSameArm ω (hyi_byi i) (hne_yi_byj i i)
        (hyi_byj i j) (hne_yi_byj i j) hnsame










theorem fac_Tcount_le_boundary_of_pairwiseCutSeparation (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (hn : 1 ≤ n) (h : fac_PairwiseCutSeparation ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  aed_Tcount_le_boundary_of_globalForestArms ω n hn
    (fac_globalForestArms_of_pairwiseCutSeparation ω n h)
















theorem fac_burton_keane_bernoulli_of_pairwiseCutSeparation (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      fac_PairwiseCutSeparation ω n)
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
  aed_burton_keane_bernoulli_of_globalForestArms hd p hp1 hp0
    (fun ω n hn => fac_globalForestArms_of_pairwiseCutSeparation ω n (hres ω n hn))
    htrif

end Percolation

end StatMech
