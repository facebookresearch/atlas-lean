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
import Code.Percolation.BKArmSelectorClose

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}




























def rts_RootedColoredForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (b : Site d → Site d) (lt : Site d → Site d → Prop) (c : Site d → Site d → Fin 3),
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → lt x y ∨ lt y x) ∧
    (∀ y, y ∈ box d n → IsTrifurcation d ω y → ∀ u v,
      Connected d ω y u → y ≠ u → Connected d ω y v → y ≠ v →
      (c y u = c y v ↔ fsp_sameArm ω y u v)) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      Connected d ω x y → lt x y → c y (b x) ≠ c y (b y))















theorem rts_rootedTreeArmSelection_of_rootedColoredForest
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : rts_RootedColoredForest ω n) :
    bas_RootedTreeArmSelection ω n := by
  classical
  obtain ⟨b, lt, c, hdata, hcomp, hcolor, hdiv⟩ := h
  refine ⟨b, lt, hdata, hcomp, ?_⟩
  intro x hxbox htri y hybox htriy hconn hlt
  set T := tfc_trifFinset ω n with hT
  
  have hyT : y ∈ T := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
  have hbxnotin : b x ∉ T := stac_infiniteCluster_notMem T ω (hdata x hxbox htri).2.2
  have hbynotin : b y ∉ T := stac_infiniteCluster_notMem T ω (hdata y hybox htriy).2.2
  
  have hne_y_bx : y ≠ b x := fun heq => hbxnotin (heq ▸ hyT)
  have hne_y_by : y ≠ b y := fun heq => hbynotin (heq ▸ hyT)
  
  have hy_bx : Connected d ω y (b x) := hconn.symm.trans (hdata x hxbox htri).2.1
  have hy_by : Connected d ω y (b y) := (hdata y hybox htriy).2.1
  
  have hcoldiff : c y (b x) ≠ c y (b y) := hdiv x hxbox htri y hybox htriy hconn hlt
  intro hsame
  exact hcoldiff ((hcolor y hybox htriy (b x) (b y) hy_bx hne_y_bx hy_by hne_y_by).mpr hsame)



theorem rts_directionalDivergence_of_rootedColoredForest (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : rts_RootedColoredForest ω n) :
    fpc_DirectionalChosenArmDivergence ω n :=
  bas_directionalDivergence_of_rootedTreeArmSelection ω n
    (rts_rootedTreeArmSelection_of_rootedColoredForest ω n h)



theorem rts_pairwiseCutSeparation_of_rootedColoredForest (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : rts_RootedColoredForest ω n) :
    fac_PairwiseCutSeparation ω n :=
  bas_pairwiseCutSeparation_of_rootedTreeArmSelection ω n
    (rts_rootedTreeArmSelection_of_rootedColoredForest ω n h)



theorem rts_globalForestArms_of_rootedColoredForest (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : rts_RootedColoredForest ω n) :
    aed_GlobalForestArms ω n :=
  bas_globalForestArms_of_rootedTreeArmSelection ω n
    (rts_rootedTreeArmSelection_of_rootedColoredForest ω n h)











theorem rts_rootedColoredForest_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    rts_RootedColoredForest ω n := by
  refine ⟨id, (fun _ _ => False), (fun _ _ => 0), ?_, ?_, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro y hybox htri; exact absurd htri (hno y hybox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)







theorem rts_rootedColoredForest_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d) (cx0 cy0 : Site d → Fin 3) (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hcx0faith : ∀ u v, Connected d ω x₀ u → x₀ ≠ u → Connected d ω x₀ v → x₀ ≠ v →
      (cx0 u = cx0 v ↔ fsp_sameArm ω x₀ u v))
    (hcy0faith : ∀ u v, Connected d ω y₀ u → y₀ ≠ u → Connected d ω y₀ v → y₀ ≠ v →
      (cy0 u = cy0 v ↔ fsp_sameArm ω y₀ u v))
    (hdeep : cy0 (b x₀) ≠ cy0 (b y₀)) :
    rts_RootedColoredForest ω n := by
  classical
  refine ⟨b, (fun u v => u = x₀ ∧ v = y₀), (fun z => if z = y₀ then cy0 else cx0),
    ?_, ?_, ?_, ?_⟩
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
    intro yy hyybox htriy u v hyu hneu hyv hnev
    rcases htwo yy hyybox htriy with rfl | rfl
    · simp only [if_neg hx0y0]; exact hcx0faith u v hyu hneu hyv hnev
    · simp only [if_pos]; exact hcy0faith u v hyu hneu hyv hnev
  · 
    intro x hxbox htri y hybox htriy _ hlt
    obtain ⟨rfl, rfl⟩ := hlt
    simpa using hdeep

















theorem rts_rootedColoredForest_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d) (y : Fin 3 → Site d) (lx : Site d → Fin 3) (ly : Fin 3 → Site d → Fin 3)
    (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i ∧
      Connected d ω x₀ (y i))
    (hyinj : Function.Injective y)
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
    rts_RootedColoredForest ω n := by
  classical
  set T := tfc_trifFinset ω n with hT
  
  have hx0T : x₀ ∈ T := tfc_mem_trifFinset.mpr ⟨hx0box, htri0⟩
  have hyT : ∀ i, y i ∈ T := fun i => tfc_mem_trifFinset.mpr ⟨(hydata i).1, (hydata i).2.1⟩
  
  have hx0y : ∀ i, x₀ ≠ y i := fun i => (hydata i).2.2.1
  
  have hbx0notin : b x₀ ∉ T := stac_infiniteCluster_notMem T ω (hbdata x₀ hx0box htri0).2.2
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
  
  set c : Site d → Site d → Fin 3 :=
    fun z => if z = x₀ then lx
             else if h : ∃ i, z = y i then ly h.choose else lx with hc
  have hcyi : ∀ i, c (y i) = ly i := by
    intro i
    have hne : y i ≠ x₀ := (hx0y i).symm
    have hex : ∃ j, y i = y j := ⟨i, rfl⟩
    rw [hc]
    simp only [if_neg hne, dif_pos hex]
    rw [hyinj hex.choose_spec.symm]
  have hcx0 : c x₀ = lx := by simp [hc]
  
  refine ⟨b, (fun u v =>
      (u = x₀ ∧ ∃ i, v = y i) ∨ (∃ i j, u = y i ∧ v = y j ∧ (i : ℕ) < j)),
    c, hbdata, ?_, ?_, ?_⟩
  · 
    intro x hxbox htri x' hx'box htri' hxx' _hconn
    rcases hsingle x hxbox htri with rfl | ⟨i, rfl⟩
    · rcases hsingle x' hx'box htri' with rfl | ⟨i, rfl⟩
      · exact absurd rfl hxx'
      · exact Or.inl (Or.inl ⟨rfl, i, rfl⟩)
    · rcases hsingle x' hx'box htri' with rfl | ⟨j, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, i, rfl⟩)
      · have hij : i ≠ j := fun h => hxx' (by rw [h])
        rcases lt_or_gt_of_ne (a := (i : ℕ)) (b := (j : ℕ))
            (fun h => hij (Fin.ext h)) with hlt | hlt
        · exact Or.inl (Or.inr ⟨i, j, rfl, rfl, hlt⟩)
        · exact Or.inr (Or.inr ⟨j, i, rfl, rfl, hlt⟩)
  · 
    intro yy hyybox htriy u v hyu hneu hyv hnev
    rcases hsingle yy hyybox htriy with rfl | ⟨i, rfl⟩
    · rw [hcx0]; exact hlxf u v hyu hneu hyv hnev
    · rw [hcyi i]; exact hlyf i u v hyu hneu hyv hnev
  · 
    intro x hxbox htri x' hx'box htri' _hconn hlt
    rcases hlt with ⟨hxe, i, hx'e⟩ | ⟨i, j, hxe, hx'e, hij⟩
    · 
      rw [hxe, hx'e, hcyi i]
      by_cases hji : (j₀ : Fin 3) = i
      · 
        subst hji; exact hcentral
      · 
        have hG_bx0 : ly i (b x₀) = 0 :=
          (hGstar i (b x₀) hx0bx0 hne_bx0 (hyi_bx0 i) (hne_yi_bx0 i)).mpr
            (by rw [hcx]; exact hji)
        have hG_byi : ly i (b (y i)) ≠ 0 :=
          (not_iff_not.mpr (hGstar i (b (y i)) (hx0byi i) (hne_x0_byi i)
            (hyi_byi i) (hne_yi_byj i i))).mpr (by rw [not_not, hcy i])
        rw [hG_bx0]; exact fun h => hG_byi h.symm
    · 
      rw [hxe, hx'e, hcyi j]
      have hij' : i ≠ j := fun h => (by rw [h] at hij; exact lt_irrefl _ hij)
      
      have hG_byi : ly j (b (y i)) = 0 :=
        (hGstar j (b (y i)) (hx0byi i) (hne_x0_byi i)
          (hyi_byj j i) (hne_yi_byj j i)).mpr (by rw [hcy i]; exact hij')
      
      have hG_byj : ly j (b (y j)) ≠ 0 :=
        (not_iff_not.mpr (hGstar j (b (y j)) (hx0byi j) (hne_x0_byi j)
          (hyi_byi j) (hne_yi_byj j j))).mpr (by rw [not_not, hcy j])
      rw [hG_byi]; exact fun h => hG_byj h.symm














theorem rts_rootedColoredForest_of_tree (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (r m : Site d) (g : Fin 2 → Site d) (b : Site d → Site d)
    (cr cm : Site d → Fin 3) (cg : Fin 2 → Site d → Fin 3)
    (hdistinct : r ≠ m ∧ (∀ i, r ≠ g i) ∧ (∀ i, m ≠ g i) ∧ Function.Injective g)
    (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = r ∨ x = m ∨ ∃ i, x = g i)
    (hbdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
    
    (hcrf : ∀ u v, Connected d ω r u → r ≠ u → Connected d ω r v → r ≠ v →
      (cr u = cr v ↔ fsp_sameArm ω r u v))
    (hcmf : ∀ u v, Connected d ω m u → m ≠ u → Connected d ω m v → m ≠ v →
      (cm u = cm v ↔ fsp_sameArm ω m u v))
    (hcgf : ∀ i u v, Connected d ω (g i) u → g i ≠ u → Connected d ω (g i) v → g i ≠ v →
      (cg i u = cg i v ↔ fsp_sameArm ω (g i) u v))
    
    (hrm : cm (b r) ≠ cm (b m)) 
    (hrg : ∀ i, cg i (b r) ≠ cg i (b (g i))) 
    (hmg : ∀ i, cg i (b m) ≠ cg i (b (g i))) 
    (hgg : cg 1 (b (g 0)) ≠ cg 1 (b (g 1))) : 
    rts_RootedColoredForest ω n := by
  classical
  obtain ⟨hrm_ne, hrg_ne, hmg_ne, hginj⟩ := hdistinct
  
  set c : Site d → Site d → Fin 3 :=
    fun z => if z = r then cr
             else if z = m then cm
             else if h : ∃ i, z = g i then cg h.choose else cr with hc
  have hcr : c r = cr := by simp [hc]
  have hcm : c m = cm := by
    have : (m = r) = False := by simp [Ne.symm hrm_ne]
    simp [hc, Ne.symm hrm_ne]
  have hcg : ∀ i, c (g i) = cg i := by
    intro i
    have h1 : g i ≠ r := (hrg_ne i).symm
    have h2 : g i ≠ m := (hmg_ne i).symm
    have hex : ∃ j, g i = g j := ⟨i, rfl⟩
    rw [hc]
    simp only [if_neg h1, if_neg h2, dif_pos hex]
    rw [hginj hex.choose_spec.symm]
  
  refine ⟨b, (fun u v =>
      (u = r ∧ v = m) ∨ (u = r ∧ ∃ i, v = g i) ∨ (u = m ∧ ∃ i, v = g i) ∨
        (∃ i j, u = g i ∧ v = g j ∧ (i : ℕ) < j)),
    c, hbdata, ?_, ?_, ?_⟩
  · 
    intro x hxbox htri x' hx'box htri' hxx' _hconn
    rcases hsingle x hxbox htri with rfl | rfl | ⟨i, rfl⟩
    · rcases hsingle x' hx'box htri' with rfl | rfl | ⟨i, rfl⟩
      · exact absurd rfl hxx'
      · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inl (Or.inr (Or.inl ⟨rfl, i, rfl⟩))
    · rcases hsingle x' hx'box htri' with rfl | rfl | ⟨i, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact absurd rfl hxx'
      · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨rfl, i, rfl⟩)))
    · rcases hsingle x' hx'box htri' with rfl | rfl | ⟨j, rfl⟩
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, i, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, i, rfl⟩)))
      · have hij : i ≠ j := fun h => hxx' (by rw [h])
        rcases lt_or_gt_of_ne (a := (i : ℕ)) (b := (j : ℕ))
            (fun h => hij (Fin.ext h)) with hlt | hlt
        · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨i, j, rfl, rfl, hlt⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨j, i, rfl, rfl, hlt⟩)))
  · 
    intro yy hyybox htriy u v hyu hneu hyv hnev
    rcases hsingle yy hyybox htriy with rfl | rfl | ⟨i, rfl⟩
    · rw [hcr]; exact hcrf u v hyu hneu hyv hnev
    · rw [hcm]; exact hcmf u v hyu hneu hyv hnev
    · rw [hcg i]; exact hcgf i u v hyu hneu hyv hnev
  · 
    intro x hxbox htri x' hx'box htri' _hconn hlt
    rcases hlt with ⟨hxe, hx'e⟩ | ⟨hxe, i, hx'e⟩ | ⟨hxe, i, hx'e⟩ | ⟨i, j, hxe, hx'e, hij⟩
    · 
      rw [hxe, hx'e, hcm]; exact hrm
    · 
      rw [hxe, hx'e, hcg i]; exact hrg i
    · 
      rw [hxe, hx'e, hcg i]; exact hmg i
    · 
      rw [hxe, hx'e]
      
      have hib : (i : ℕ) < 2 := i.isLt
      have hjb : (j : ℕ) < 2 := j.isLt
      have hi0 : i = 0 := Fin.ext (by omega)
      have hj1 : j = 1 := Fin.ext (by omega)
      subst hi0; subst hj1
      rw [hcg 1]; exact hgg









theorem rts_Tcount_le_boundary_of_rootedColoredForest (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (hn : 1 ≤ n) (h : rts_RootedColoredForest ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bas_Tcount_le_boundary_of_rootedTreeArmSelection ω n hn
    (rts_rootedTreeArmSelection_of_rootedColoredForest ω n h)

















theorem rts_burton_keane_bernoulli_of_rootedColoredForest (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      rts_RootedColoredForest ω n)
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
  bas_burton_keane_bernoulli_of_rootedTreeArmSelection hd p hp1 hp0
    (fun ω n hn => rts_rootedTreeArmSelection_of_rootedColoredForest ω n (hres ω n hn))
    htrif

end Percolation

end StatMech
