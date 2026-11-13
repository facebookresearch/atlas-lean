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
import Code.Percolation.RootedTreeSelectorClose
import Code.Percolation.SpanningTreeTrifClose
import Code.Percolation.ForestColouringClose2

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}


























theorem rfp_root_arm_obstruction (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {b : Site d → Site d} {rank : Site d → ℕ ×ₗ ℕ} {x₀ z : Site d}
    (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hzbox : z ∈ box d n) (htriz : IsTrifurcation d ω z)
    (hne : x₀ ≠ z) (hconn : Connected d ω x₀ z)
    (hrank : rank x₀ ≠ rank z)
    (hpair : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x < rank y →
      Connected d (removeSite y ω) (b x) x ∧ ¬ Connected d (removeSite y ω) (b y) x)
    (hbeyond : Connected d (removeSite x₀ ω) (b x₀) z)
    (hcrossed : ¬ Connected d (removeSite z ω) (b x₀) x₀) :
    False := by
  rcases lt_trichotomy (rank x₀) (rank z) with hlt | heq | hgt
  · 
    obtain ⟨hfar, _hpriv⟩ := hpair x₀ hx0box htri0 z hzbox htriz hne hconn hlt
    
    exact hcrossed hfar
  · exact hrank heq
  · 
    obtain ⟨_hfar, hpriv⟩ :=
      hpair z hzbox htriz x₀ hx0box htri0 hne.symm hconn.symm hgt
    
    exact hpriv hbeyond



















noncomputable def rfp_p0 : Site 1 := fun _ => 0

noncomputable def rfp_p1 : Site 1 := fun _ => 1

noncomputable def rfp_p2 : Site 1 := fun _ => 2


noncomputable def rfp_ωpath : ConfigSpace (Sym2 (Site 1)) :=
  fun e => decide (e = s(rfp_p0, rfp_p1) ∨ e = s(rfp_p1, rfp_p2))



theorem rfp_consistency_beyond :
    Connected 1 (removeSite rfp_p0 rfp_ωpath) rfp_p2 rfp_p1 := by
  refine SimpleGraph.Adj.reachable (G := openSubgraph 1 (removeSite rfp_p0 rfp_ωpath)) ?_
  refine ⟨?_, ?_⟩
  · rw [hypercubicLattice_adj]; simp [rfp_p1, rfp_p2]
  · have hp0 : rfp_p0 ∉ s(rfp_p2, rfp_p1) := by
      simp only [Sym2.mem_iff, not_or]
      refine ⟨?_, ?_⟩
      · intro h; have := congrFun h ⟨0, by norm_num⟩; simp [rfp_p0, rfp_p2] at this
      · intro h; have := congrFun h ⟨0, by norm_num⟩; simp [rfp_p0, rfp_p1] at this
    rw [removeSite_apply_of_notMem hp0]
    change decide (s(rfp_p2, rfp_p1) = s(rfp_p0, rfp_p1) ∨ s(rfp_p2, rfp_p1) = s(rfp_p1, rfp_p2))
        = true
    simp only [decide_eq_true_eq]
    right; rw [Sym2.eq_swap]


theorem rfp_path_noEdge_after_p1 (a b : Site 1) :
    ¬ (openSubgraph 1 (removeSite rfp_p1 rfp_ωpath)).Adj a b := by
  rintro ⟨_hadj, hopen⟩
  by_cases hp1 : rfp_p1 ∈ s(a, b)
  · rw [removeSite_apply_of_mem hp1] at hopen; exact Bool.false_ne_true hopen
  · rw [removeSite_apply_of_notMem hp1] at hopen
    have h2 : s(a, b) = s(rfp_p0, rfp_p1) ∨ s(a, b) = s(rfp_p1, rfp_p2) := by
      simpa only [rfp_ωpath, decide_eq_true_eq] using hopen
    rcases h2 with h | h
    · exact hp1 (h ▸ Sym2.mem_mk_right rfp_p0 rfp_p1)
    · exact hp1 (h ▸ Sym2.mem_mk_left rfp_p1 rfp_p2)


theorem rfp_path_conn_eq_after_p1 {a b : Site 1}
    (h : Connected 1 (removeSite rfp_p1 rfp_ωpath) a b) : a = b := by
  obtain ⟨w⟩ := h
  cases w with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (rfp_path_noEdge_after_p1 _ _)



theorem rfp_consistency_crossed :
    ¬ Connected 1 (removeSite rfp_p1 rfp_ωpath) rfp_p2 rfp_p0 := by
  intro h
  have heq := rfp_path_conn_eq_after_p1 h
  have := congrFun heq ⟨0, by norm_num⟩
  simp [rfp_p0, rfp_p2] at this






theorem rfp_armGeometry_consistent :
    ∃ (ω : ConfigSpace (Sym2 (Site 1))) (x₀ z w : Site 1),
      Connected 1 (removeSite x₀ ω) w z ∧ ¬ Connected 1 (removeSite z ω) w x₀ :=
  ⟨rfp_ωpath, rfp_p0, rfp_p1, rfp_p2, rfp_consistency_beyond, rfp_consistency_crossed⟩



























def rfp_ClawArmGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ x₀ : Site d, x₀ ∈ box d n ∧ IsTrifurcation d ω x₀ ∧
    ∀ b : Site d → Site d,
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite →
      ∃ z, z ∈ box d n ∧ IsTrifurcation d ω z ∧ x₀ ≠ z ∧ Connected d ω x₀ z ∧
        Connected d (removeSite x₀ ω) (b x₀) z ∧
        ¬ Connected d (removeSite z ω) (b x₀) x₀






theorem rfp_not_rootedPrivateArm_of_clawArmGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : rfp_ClawArmGeometry ω n) :
    ¬ fcc_RootedPrivateArm ω n := by
  rintro ⟨b, rank, hbdata, hrank, hpair⟩
  obtain ⟨x₀, hx0box, htri0, harm⟩ := hgeo
  
  have hbx0inf : (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite :=
    (hbdata x₀ hx0box htri0).2.2
  
  obtain ⟨z, hzbox, htriz, hne, hconn, hbeyond, hcrossed⟩ := harm b hbx0inf
  
  have hrk : rank x₀ ≠ rank z := hrank x₀ hx0box htri0 z hzbox htriz hne hconn
  exact rfp_root_arm_obstruction ω n hx0box htri0 hzbox htriz hne hconn hrk hpair
    hbeyond hcrossed















theorem rfp_clawArmGeometry_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d) (y : Fin 3 → Site d)
    (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i ∧
      Connected d ω x₀ (y i))
    (hcross : ∀ b : Site d → Site d,
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite →
      ∃ i, Connected d (removeSite x₀ ω) (b x₀) (y i) ∧
        ¬ Connected d (removeSite (y i) ω) (b x₀) x₀) :
    rfp_ClawArmGeometry ω n := by
  refine ⟨x₀, hx0box, htri0, ?_⟩
  intro b hbinf
  obtain ⟨i, hbeyond, hcrossed⟩ := hcross b hbinf
  exact ⟨y i, (hydata i).1, (hydata i).2.1, (hydata i).2.2.1, (hydata i).2.2.2,
    hbeyond, hcrossed⟩







theorem rfp_rootedPrivateArm_refutable (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hgeo : rfp_ClawArmGeometry ω n) :
    ¬ fcc_RootedPrivateArm ω n :=
  rfp_not_rootedPrivateArm_of_clawArmGeometry ω n hgeo












def rfp_RootedArmDivergence (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (b : Site d → Site d) (rank : Site d → ℕ ×ₗ ℕ),
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x ≠ rank y) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x < rank y →
      ¬ fsp_sameArm ω y (b x) (b y))






theorem rfp_rootedSingleCutSeparation_of_armDivergence (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : rfp_RootedArmDivergence ω n) :
    fcc_RootedSingleCutSeparation ω n := by
  obtain ⟨b, rank, hbdata, hrank, hdiv⟩ := h
  refine ⟨b, rank, hbdata, hrank, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  have hyT : y ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
  have hbxnotin : b x ∉ tfc_trifFinset ω n :=
    stac_infiniteCluster_notMem (tfc_trifFinset ω n) ω (hbdata x hxbox htri).2.2
  have hbynotin : b y ∉ tfc_trifFinset ω n :=
    stac_infiniteCluster_notMem (tfc_trifFinset ω n) ω (hbdata y hybox htriy).2.2
  have hne_y_bx : y ≠ b x := fun heq => hbxnotin (heq ▸ hyT)
  have hne_y_by : y ≠ b y := fun heq => hbynotin (heq ▸ hyT)
  have hy_bx : Connected d ω y (b x) := hconn.symm.trans (hbdata x hxbox htri).2.1
  have hy_by : Connected d ω y (b y) := (hbdata y hybox htriy).2.1
  exact fsp_sep_of_notSameArm ω hy_bx hne_y_bx hy_by hne_y_by
    (hdiv x hxbox htri y hybox htriy hxy hconn hlt)








theorem rfp_rootedArmDivergence_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    rfp_RootedArmDivergence ω n := by
  refine ⟨id, (fun _ => toLex (0, 0)), ?_, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)




theorem rfp_rootedArmDivergence_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d) (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hdeep : ¬ fsp_sameArm ω y₀ (b x₀) (b y₀)) :
    rfp_RootedArmDivergence ω n := by
  classical
  refine ⟨b, (fun z => if z = y₀ then toLex (1, 0) else toLex (0, 0)), ?_, ?_, ?_⟩
  · intro x hxbox htri
    rcases htwo x hxbox htri with rfl | rfl
    · exact hbx0
    · exact hby0
  · intro x hxbox htri x' hx'box htri' hxx' _
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo x' hx'box htri' with rfl | rfl
      · exact absurd rfl hxx'
      · simp only [if_neg hx0y0, if_pos]; exact stt_lex_ne_fst (by norm_num)
    · rcases htwo x' hx'box htri' with rfl | rfl
      · simp only [if_neg hx0y0, if_pos]; exact stt_lex_ne_fst (by norm_num)
      · exact absurd rfl hxx'
  · intro x hxbox htri x' hx'box htri' hxx' _ hlt
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo x' hx'box htri' with rfl | rfl
      · exact absurd rfl hxx'
      · exact hdeep
    · rcases htwo x' hx'box htri' with rfl | rfl
      · simp only [if_neg hx0y0, if_pos] at hlt
        exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
      · exact absurd rfl hxx'






theorem rfp_rootedArmDivergence_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d) (y : Fin 3 → Site d) (lx : Site d → Fin 3) (ly : Fin 3 → Site d → Fin 3)
    (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i ∧
      Connected d ω x₀ (y i))
    (hyinj : Function.Injective y)
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
    rfp_RootedArmDivergence ω n := by
  
  obtain ⟨b', rank, hbdata', hrank, hsep⟩ :=
    fcc_rootedSingleCutSeparation_of_claw ω n x₀ y lx ly hx0box htri0 hydata hyinj hlyf hGstar
      hsingle b hbdata hcy hcx hcentral
  refine ⟨b', rank, hbdata', hrank, ?_⟩
  intro x hxbox htri y' hy'box htriy' hxy hconn hlt
  
  have hy'T : y' ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hy'box, htriy'⟩
  have hbxnotin : b' x ∉ tfc_trifFinset ω n :=
    stac_infiniteCluster_notMem (tfc_trifFinset ω n) ω (hbdata' x hxbox htri).2.2
  have hbynotin : b' y' ∉ tfc_trifFinset ω n :=
    stac_infiniteCluster_notMem (tfc_trifFinset ω n) ω (hbdata' y' hy'box htriy').2.2
  have hne_y_bx : y' ≠ b' x := fun heq => hbxnotin (heq ▸ hy'T)
  have hne_y_by : y' ≠ b' y' := fun heq => hbynotin (heq ▸ hy'T)
  have hy_bx : Connected d ω y' (b' x) := hconn.symm.trans (hbdata' x hxbox htri).2.1
  have hy_by : Connected d ω y' (b' y') := (hbdata' y' hy'box htriy').2.1
  exact fcc_notSameArm_of_singleCut ω hy_bx hne_y_bx hy_by hne_y_by
    (hsep x hxbox htri y' hy'box htriy' hxy hconn hlt)









theorem rfp_rootedSpanningForest_of_coverArmDivergence (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hcov : fcc_ThreeArmCover ω n) (hdiv : rfp_RootedArmDivergence ω n) :
    stt_RootedSpanningForest ω n :=
  fcc_rootedSpanningForest_of_coverSep ω n hcov
    (rfp_rootedSingleCutSeparation_of_armDivergence ω n hdiv)


theorem rfp_Tcount_le_boundary_of_coverArmDivergence (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (hcov : fcc_ThreeArmCover ω n) (hdiv : rfp_RootedArmDivergence ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  stt_Tcount_le_boundary_of_rootedSpanningForest ω n hn
    (rfp_rootedSpanningForest_of_coverArmDivergence ω n hcov hdiv)













theorem rfp_burton_keane_bernoulli_of_coverArmDivergence (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hcov : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fcc_ThreeArmCover ω n)
    (hdiv : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → rfp_RootedArmDivergence ω n)
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
  stt_burton_keane_bernoulli_of_rootedSpanningForest hd p hp1 hp0
    (fun ω n hn => rfp_rootedSpanningForest_of_coverArmDivergence ω n (hcov ω n hn) (hdiv ω n hn))
    htrif

end Percolation

end StatMech
