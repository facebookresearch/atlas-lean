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

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}










def fcc_ThreeArmCover (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ arms : Site d → Fin 3 → Site d,
    ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      (∀ i j, i ≠ j → ¬ Connected d (removeSite y ω) (arms y i) (arms y j)) ∧
      (∀ w, Connected d ω y w → y ≠ w →
        ∃ i, Connected d (removeSite y ω) (arms y i) (fsp_armWitness ω y w))






def fcc_RootedSingleCutSeparation (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (b : Site d → Site d) (rank : Site d → ℕ ×ₗ ℕ),
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x ≠ rank y) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x < rank y →
      ¬ Connected d (removeSite y ω) (b x) (b y))











theorem fcc_notSameArm_of_singleCut (ω : ConfigSpace (Sym2 (Site d))) {y u v : Site d}
    (hyu : Connected d ω y u) (hneu : y ≠ u)
    (hyv : Connected d ω y v) (hnev : y ≠ v)
    (hsep : ¬ Connected d (removeSite y ω) u v) :
    ¬ fsp_sameArm ω y u v := by
  intro hsame
  unfold fsp_sameArm at hsame
  have hwu : Connected d (removeSite y ω) (fsp_armWitness ω y u) u :=
    fsp_armWitness_inArm ω hyu hneu
  have hwv : Connected d (removeSite y ω) (fsp_armWitness ω y v) v :=
    fsp_armWitness_inArm ω hyv hnev
  exact hsep (hwu.symm.trans (hsame.trans hwv))









open Classical in


noncomputable def fcc_colorRep (ω : ConfigSpace (Sym2 (Site d))) (c : Site d → Site d → Fin 3)
    (y : Site d) (i : Fin 3) : Site d :=
  if h : ∃ w, Connected d ω y w ∧ y ≠ w ∧ c y w = i then h.choose else y



theorem fcc_removeSite_self_eq (ω : ConfigSpace (Sym2 (Site d))) {y v : Site d}
    (h : Connected d (removeSite y ω) y v) : v = y := by
  have h' : Connected d (removeSites {y} ω) y v := by rwa [daep_removeSites_singleton]
  exact stac_removeSites_connected_eq {y} ω (Finset.mem_singleton_self y) h'




theorem fcc_two_distinct_arms (ω : ConfigSpace (Sym2 (Site d))) {y : Site d}
    (htri : IsTrifurcation d ω y) :
    ∃ u v, (Connected d ω y u ∧ y ≠ u) ∧ (Connected d ω y v ∧ y ≠ v) ∧
      ¬ fsp_sameArm ω y u v := by
  obtain ⟨a₁, a₂, a₃, ⟨h12, h13, h23⟩, ⟨hc1, hc2, hc3⟩, _hinf, ⟨hd12, hd13, hd23⟩⟩ := htri
  by_cases e1 : y = a₁
  · have ne2 : y ≠ a₂ := fun h => h12 (e1.symm.trans h)
    have ne3 : y ≠ a₃ := fun h => h13 (e1.symm.trans h)
    exact ⟨a₂, a₃, ⟨hc2, ne2⟩, ⟨hc3, ne3⟩, fcc_notSameArm_of_singleCut ω hc2 ne2 hc3 ne3 hd23⟩
  · by_cases e2 : y = a₂
    · have ne3 : y ≠ a₃ := fun h => h23 (e2.symm.trans h)
      exact ⟨a₁, a₃, ⟨hc1, e1⟩, ⟨hc3, ne3⟩, fcc_notSameArm_of_singleCut ω hc1 e1 hc3 ne3 hd13⟩
    · exact ⟨a₁, a₂, ⟨hc1, e1⟩, ⟨hc2, e2⟩, fcc_notSameArm_of_singleCut ω hc1 e1 hc2 e2 hd12⟩





theorem fcc_threeArmCover_of_faithful (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (c : Site d → Site d → Fin 3)
    (hcolor : ∀ y, y ∈ box d n → IsTrifurcation d ω y → ∀ u v,
      Connected d ω y u → y ≠ u → Connected d ω y v → y ≠ v →
      (c y u = c y v ↔ fsp_sameArm ω y u v)) :
    fcc_ThreeArmCover ω n := by
  classical
  refine ⟨fcc_colorRep ω c, ?_⟩
  intro y hybox htriy
  have hrep_real : ∀ i, (∃ w, Connected d ω y w ∧ y ≠ w ∧ c y w = i) →
      Connected d ω y (fcc_colorRep ω c y i) ∧ y ≠ fcc_colorRep ω c y i ∧
      c y (fcc_colorRep ω c y i) = i := by
    intro i hex
    rw [fcc_colorRep, dif_pos hex]; exact hex.choose_spec
  
  have hcover : ∀ w, Connected d ω y w → y ≠ w →
      ∃ i, Connected d (removeSite y ω) (fcc_colorRep ω c y i) (fsp_armWitness ω y w) := by
    intro w hyw hnew
    refine ⟨c y w, ?_⟩
    have hex : ∃ w', Connected d ω y w' ∧ y ≠ w' ∧ c y w' = c y w := ⟨w, hyw, hnew, rfl⟩
    obtain ⟨hr_conn, hr_ne, hr_col⟩ := hrep_real (c y w) hex
    have hsame : fsp_sameArm ω y (fcc_colorRep ω c y (c y w)) w :=
      (hcolor y hybox htriy _ _ hr_conn hr_ne hyw hnew).mp hr_col
    unfold fsp_sameArm at hsame
    have hwr : Connected d (removeSite y ω) (fsp_armWitness ω y (fcc_colorRep ω c y (c y w)))
        (fcc_colorRep ω c y (c y w)) := fsp_armWitness_inArm ω hr_conn hr_ne
    exact hwr.symm.trans hsame
  
  have hsep : ∀ i j, i ≠ j →
      ¬ Connected d (removeSite y ω) (fcc_colorRep ω c y i) (fcc_colorRep ω c y j) := by
    intro i j hij hconn
    by_cases hi : ∃ w, Connected d ω y w ∧ y ≠ w ∧ c y w = i
    · by_cases hj : ∃ w, Connected d ω y w ∧ y ≠ w ∧ c y w = j
      · obtain ⟨hi_conn, hi_ne, hi_col⟩ := hrep_real i hi
        obtain ⟨hj_conn, hj_ne, hj_col⟩ := hrep_real j hj
        have hcd : c y (fcc_colorRep ω c y i) ≠ c y (fcc_colorRep ω c y j) := by
          rw [hi_col, hj_col]; exact hij
        have hns : ¬ fsp_sameArm ω y (fcc_colorRep ω c y i) (fcc_colorRep ω c y j) := fun hsame =>
          hcd ((hcolor y hybox htriy _ _ hi_conn hi_ne hj_conn hj_ne).mpr hsame)
        apply hns
        unfold fsp_sameArm
        have hwi : Connected d (removeSite y ω) (fsp_armWitness ω y (fcc_colorRep ω c y i))
            (fcc_colorRep ω c y i) := fsp_armWitness_inArm ω hi_conn hi_ne
        have hwj : Connected d (removeSite y ω) (fsp_armWitness ω y (fcc_colorRep ω c y j))
            (fcc_colorRep ω c y j) := fsp_armWitness_inArm ω hj_conn hj_ne
        exact hwi.trans (hconn.trans hwj.symm)
      · obtain ⟨_, hi_ne, _⟩ := hrep_real i hi
        have hjy : fcc_colorRep ω c y j = y := by rw [fcc_colorRep, dif_neg hj]
        rw [hjy] at hconn
        exact hi_ne (fcc_removeSite_self_eq ω hconn.symm).symm
    · have hiy : fcc_colorRep ω c y i = y := by rw [fcc_colorRep, dif_neg hi]
      rw [hiy] at hconn
      have hjy : fcc_colorRep ω c y j = y := fcc_removeSite_self_eq ω hconn
      by_cases hj : ∃ w, Connected d ω y w ∧ y ≠ w ∧ c y w = j
      · obtain ⟨_, hj_ne, _⟩ := hrep_real j hj
        exact hj_ne hjy.symm
      · 
        obtain ⟨u, v, ⟨hyu, hneu⟩, ⟨hyv, hnev⟩, huv⟩ := fcc_two_distinct_arms ω htriy
        have hcuv : c y u ≠ c y v := fun hce =>
          huv ((hcolor y hybox htriy u v hyu hneu hyv hnev).mp hce)
        have hu_i : c y u ≠ i := fun he => hi ⟨u, hyu, hneu, he⟩
        have hu_j : c y u ≠ j := fun he => hj ⟨u, hyu, hneu, he⟩
        have hv_i : c y v ≠ i := fun he => hi ⟨v, hyv, hnev, he⟩
        have hv_j : c y v ≠ j := fun he => hj ⟨v, hyv, hnev, he⟩
        have hle : ({c y u, c y v, i, j} : Finset (Fin 3)).card ≤ Fintype.card (Fin 3) :=
          Finset.card_le_univ _
        have hcard : ({c y u, c y v, i, j} : Finset (Fin 3)).card = 4 := by
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
            Finset.card_insert_of_notMem, Finset.card_singleton]
          · rw [Finset.mem_singleton]; exact hij
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hv_i, hv_j⟩
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hcuv, hu_i, hu_j⟩
        rw [hcard, Fintype.card_fin] at hle
        omega
  exact ⟨hsep, hcover⟩












theorem fcc_rootedSpanningForest_of_coverSep (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hcov : fcc_ThreeArmCover ω n) (hsep : fcc_RootedSingleCutSeparation ω n) :
    stt_RootedSpanningForest ω n := by
  classical
  obtain ⟨arms, harms⟩ := hcov
  obtain ⟨b, rank, hbdata, hrank, hbsep⟩ := hsep
  refine ⟨b, rank, (fun y => stac_colorOf ω y (arms y)), hbdata, ?_, hrank, ?_⟩
  · 
    intro y hybox htriy u v hyu hneu hyv hnev
    obtain ⟨hsep', hcov'⟩ := harms y hybox htriy
    exact stac_colorOf_faithful ω y (arms y) hsep' hcov' hyu hneu hyv hnev
  · 
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
    have hsingleCut : ¬ Connected d (removeSite y ω) (b x) (b y) :=
      hbsep x hxbox htri y hybox htriy hxy hconn hlt
    have hdiv : ¬ fsp_sameArm ω y (b x) (b y) :=
      fcc_notSameArm_of_singleCut ω hy_bx hne_y_bx hy_by hne_y_by hsingleCut
    obtain ⟨hsep', hcov'⟩ := harms y hybox htriy
    intro hcoleq
    exact hdiv
      ((stac_colorOf_faithful ω y (arms y) hsep' hcov' hy_bx hne_y_bx hy_by hne_y_by).mp hcoleq)



theorem fcc_threeArmCover_of_rootedSpanningForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : stt_RootedSpanningForest ω n) : fcc_ThreeArmCover ω n := by
  obtain ⟨_b, _rank, c, _hbdata, hcolor, _hinj, _hdiv⟩ := h
  exact fcc_threeArmCover_of_faithful ω n c hcolor




theorem fcc_rootedSingleCutSeparation_of_rootedSpanningForest (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : stt_RootedSpanningForest ω n) : fcc_RootedSingleCutSeparation ω n := by
  classical
  obtain ⟨b, rank, c, hbdata, hcolor, hinj, hdiv⟩ := h
  refine ⟨b, rank, hbdata, hinj, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  have hcoldiff : c y (b x) ≠ c y (b y) := hdiv x hxbox htri y hybox htriy hxy hconn hlt
  have hyT : y ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
  have hbxnotin : b x ∉ tfc_trifFinset ω n :=
    stac_infiniteCluster_notMem (tfc_trifFinset ω n) ω (hbdata x hxbox htri).2.2
  have hbynotin : b y ∉ tfc_trifFinset ω n :=
    stac_infiniteCluster_notMem (tfc_trifFinset ω n) ω (hbdata y hybox htriy).2.2
  have hne_y_bx : y ≠ b x := fun heq => hbxnotin (heq ▸ hyT)
  have hne_y_by : y ≠ b y := fun heq => hbynotin (heq ▸ hyT)
  have hy_bx : Connected d ω y (b x) := hconn.symm.trans (hbdata x hxbox htri).2.1
  have hy_by : Connected d ω y (b y) := (hbdata y hybox htriy).2.1
  have hns : ¬ fsp_sameArm ω y (b x) (b y) := by
    intro hsame
    exact hcoldiff ((hcolor y hybox htriy (b x) (b y) hy_bx hne_y_bx hy_by hne_y_by).mpr hsame)
  exact fsp_sep_of_notSameArm ω hy_bx hne_y_bx hy_by hne_y_by hns


theorem fcc_rootedSpanningForest_iff (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    stt_RootedSpanningForest ω n ↔
      (fcc_ThreeArmCover ω n ∧ fcc_RootedSingleCutSeparation ω n) :=
  ⟨fun h => ⟨fcc_threeArmCover_of_rootedSpanningForest ω n h,
      fcc_rootedSingleCutSeparation_of_rootedSpanningForest ω n h⟩,
    fun ⟨hcov, hsep⟩ => fcc_rootedSpanningForest_of_coverSep ω n hcov hsep⟩


















def fcc_RootedPrivateArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (b : Site d → Site d) (rank : Site d → ℕ ×ₗ ℕ),
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x ≠ rank y) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x < rank y →
      Connected d (removeSite y ω) (b x) x ∧ ¬ Connected d (removeSite y ω) (b y) x)




theorem fcc_rootedSingleCutSeparation_of_rootedPrivateArm (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : fcc_RootedPrivateArm ω n) : fcc_RootedSingleCutSeparation ω n := by
  obtain ⟨b, rank, hbdata, hrank, hpair⟩ := h
  refine ⟨b, rank, hbdata, hrank, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hfar, hpriv⟩ := hpair x hxbox htri y hybox htriy hxy hconn hlt
  intro hbxby
  
  exact hpriv (hbxby.symm.trans hfar)





theorem fcc_rootedSpanningForest_of_armsPrivate (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hcov : fcc_ThreeArmCover ω n) (hpriv : fcc_RootedPrivateArm ω n) :
    stt_RootedSpanningForest ω n :=
  fcc_rootedSpanningForest_of_coverSep ω n hcov
    (fcc_rootedSingleCutSeparation_of_rootedPrivateArm ω n hpriv)



theorem fcc_rootedSpanningForest_of_coverPrivate (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hcov : fcc_ThreeArmCover ω n) (hpriv : fcc_RootedPrivateArm ω n) :
    stt_RootedSpanningForest ω n :=
  fcc_rootedSpanningForest_of_armsPrivate ω n hcov hpriv


theorem fcc_Tcount_le_boundary_of_armsPrivate (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (hcov : fcc_ThreeArmCover ω n) (hpriv : fcc_RootedPrivateArm ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  stt_Tcount_le_boundary_of_rootedSpanningForest ω n hn
    (fcc_rootedSpanningForest_of_armsPrivate ω n hcov hpriv)













theorem fcc_burton_keane_bernoulli_of_armsPrivate (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hcov : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fcc_ThreeArmCover ω n)
    (hpriv : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fcc_RootedPrivateArm ω n)
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
    (fun ω n hn => fcc_rootedSpanningForest_of_armsPrivate ω n (hcov ω n hn) (hpriv ω n hn))
    htrif








theorem fcc_threeArmCover_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    fcc_ThreeArmCover ω n := by
  refine ⟨fun _ _ => (0 : Site d), ?_⟩
  intro y hybox htriy; exact absurd htriy (hno y hybox)





theorem fcc_threeArmCover_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d) (y : Fin 3 → Site d) (lx : Site d → Fin 3) (ly : Fin 3 → Site d → Fin 3)
    (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i ∧
      Connected d ω x₀ (y i))
    (hyinj : Function.Injective y)
    (hlxf : ∀ u v, Connected d ω x₀ u → x₀ ≠ u → Connected d ω x₀ v → x₀ ≠ v →
      (lx u = lx v ↔ fsp_sameArm ω x₀ u v))
    (hlyf : ∀ i u v, Connected d ω (y i) u → y i ≠ u → Connected d ω (y i) v → y i ≠ v →
      (ly i u = ly i v ↔ fsp_sameArm ω (y i) u v))
    (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i) :
    fcc_ThreeArmCover ω n := by
  classical
  have hx0y : ∀ i, x₀ ≠ y i := fun i => (hydata i).2.2.1
  
  set c : Site d → Site d → Fin 3 :=
    fun z => if z = x₀ then lx
             else if h : ∃ i, z = y i then ly h.choose else lx with hc
  have hcyi : ∀ i, c (y i) = ly i := by
    intro i
    have hne : y i ≠ x₀ := (hx0y i).symm
    have hex : ∃ j, y i = y j := ⟨i, rfl⟩
    rw [hc]; simp only [if_neg hne, dif_pos hex]; rw [hyinj hex.choose_spec.symm]
  have hcx0 : c x₀ = lx := by simp [hc]
  refine fcc_threeArmCover_of_faithful ω n c ?_
  intro yy hyybox htriy u v hyu hneu hyv hnev
  rcases hsingle yy hyybox htriy with rfl | ⟨i, rfl⟩
  · rw [hcx0]; exact hlxf u v hyu hneu hyv hnev
  · rw [hcyi i]; exact hlyf i u v hyu hneu hyv hnev








theorem fcc_rootedPrivateArm_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    fcc_RootedPrivateArm ω n := by
  refine ⟨id, (fun _ => toLex (0, 0)), ?_, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)





theorem fcc_rootedPrivateArm_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d) (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hfar : Connected d (removeSite y₀ ω) (b x₀) x₀)
    (hpriv : ¬ Connected d (removeSite y₀ ω) (b y₀) x₀) :
    fcc_RootedPrivateArm ω n := by
  classical
  refine ⟨b, (fun z => if z = y₀ then toLex (1, 0) else toLex (0, 0)), ?_, ?_, ?_⟩
  · 
    intro x hxbox htri
    rcases htwo x hxbox htri with rfl | rfl
    · exact hbx0
    · exact hby0
  · 
    intro x hxbox htri x' hx'box htri' hxx' _
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo x' hx'box htri' with rfl | rfl
      · exact absurd rfl hxx'
      · simp only [if_neg hx0y0, if_pos]; exact stt_lex_ne_fst (by norm_num)
    · rcases htwo x' hx'box htri' with rfl | rfl
      · simp only [if_neg hx0y0, if_pos]; exact (stt_lex_ne_fst (by norm_num))
      · exact absurd rfl hxx'
  · 
    intro x hxbox htri x' hx'box htri' hxx' _ hlt
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo x' hx'box htri' with rfl | rfl
      · exact absurd rfl hxx'
      · 
        exact ⟨hfar, hpriv⟩
    · rcases htwo x' hx'box htri' with rfl | rfl
      · 
        simp only [if_neg hx0y0, if_pos] at hlt
        exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
      · exact absurd rfl hxx'










theorem fcc_rootedSingleCutSeparation_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    fcc_RootedSingleCutSeparation ω n := by
  refine ⟨id, (fun _ => toLex (0, 0)), ?_, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)






theorem fcc_rootedSingleCutSeparation_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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
    fcc_RootedSingleCutSeparation ω n := by
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
  
  set rk : Site d → ℕ ×ₗ ℕ :=
    fun z => if z = x₀ then toLex (0, 0)
             else if h : ∃ i, z = y i then toLex (1, (h.choose : ℕ)) else toLex (2, 0) with hrk
  have hrkx0 : rk x₀ = toLex (0, 0) := by simp [hrk]
  have hrkyi : ∀ i, rk (y i) = toLex (1, (i : ℕ)) := by
    intro i
    have hne : y i ≠ x₀ := (hx0y i).symm
    have hex : ∃ j, y i = y j := ⟨i, rfl⟩
    rw [hrk]; simp only [if_neg hne, dif_pos hex]; rw [hyinj hex.choose_spec.symm]
  refine ⟨b, rk, hbdata, ?_, ?_⟩
  · 
    intro x hxbox htri x' hx'box htri' hxx' _hconn
    rcases hsingle x hxbox htri with rfl | ⟨i, rfl⟩
    · rcases hsingle x' hx'box htri' with rfl | ⟨i, rfl⟩
      · exact absurd rfl hxx'
      · rw [hrkx0, hrkyi i]; exact stt_lex_ne_fst (by norm_num)
    · rcases hsingle x' hx'box htri' with rfl | ⟨j, rfl⟩
      · rw [hrkx0, hrkyi i]; exact (stt_lex_ne_fst (by norm_num)).symm
      · rw [hrkyi i, hrkyi j]
        refine stt_lex_ne_snd ?_
        intro hij; exact hxx' (by rw [Fin.val_inj.mp hij])
  · 
    intro x hxbox htri x' hx'box htri' hxx' _hconn hlt
    rcases hsingle x hxbox htri with rfl | ⟨i, rfl⟩
    · rcases hsingle x' hx'box htri' with rfl | ⟨i, rfl⟩
      · exact absurd rfl hxx'
      · 
        refine fsp_sep_of_notSameArm ω (hyi_bx0 i) (hne_yi_bx0 i) (hyi_byi i)
          (hne_yi_byj i i) ?_
        by_cases hji : (j₀ : Fin 3) = i
        · subst hji
          intro hsame
          exact hcentral ((hlyf j₀ (b x) (b (y j₀)) (hyi_bx0 j₀) (hne_yi_bx0 j₀)
            (hyi_byi j₀) (hne_yi_byj j₀ j₀)).mpr hsame)
        · intro hsame
          have hG_bx0 : ly i (b x) = 0 :=
            (hGstar i (b x) hx0bx0 hne_bx0 (hyi_bx0 i) (hne_yi_bx0 i)).mpr
              (by rw [hcx]; exact hji)
          have hG_byi : ly i (b (y i)) ≠ 0 :=
            (not_iff_not.mpr (hGstar i (b (y i)) (hx0byi i) (hne_x0_byi i)
              (hyi_byi i) (hne_yi_byj i i))).mpr (by rw [not_not, hcy i])
          have hcolly : ly i (b x) ≠ ly i (b (y i)) := by
            rw [hG_bx0]; exact fun h => hG_byi h.symm
          exact hcolly ((hlyf i (b x) (b (y i)) (hyi_bx0 i) (hne_yi_bx0 i)
            (hyi_byi i) (hne_yi_byj i i)).mpr hsame)
    · rcases hsingle x' hx'box htri' with rfl | ⟨j, rfl⟩
      · 
        rw [hrkx0, hrkyi i] at hlt
        exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
      · 
        have hij' : i ≠ j := fun h => hxx' (by rw [h])
        refine fsp_sep_of_notSameArm ω (hyi_byj j i) (hne_yi_byj j i) (hyi_byi j)
          (hne_yi_byj j j) ?_
        intro hsame
        have hG_byi : ly j (b (y i)) = 0 :=
          (hGstar j (b (y i)) (hx0byi i) (hne_x0_byi i)
            (hyi_byj j i) (hne_yi_byj j i)).mpr (by rw [hcy i]; exact hij')
        have hG_byj : ly j (b (y j)) ≠ 0 :=
          (not_iff_not.mpr (hGstar j (b (y j)) (hx0byi j) (hne_x0_byi j)
            (hyi_byi j) (hne_yi_byj j j))).mpr (by rw [not_not, hcy j])
        have hcolly : ly j (b (y i)) ≠ ly j (b (y j)) := by
          rw [hG_byi]; exact fun h => hG_byj h.symm
        exact hcolly ((hlyf j (b (y i)) (b (y j)) (hyi_byj j i) (hne_yi_byj j i)
          (hyi_byi j) (hne_yi_byj j j)).mpr hsame)










theorem fcc_rootedSpanningForest_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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
    stt_RootedSpanningForest ω n :=
  fcc_rootedSpanningForest_of_coverSep ω n
    (fcc_threeArmCover_of_claw ω n x₀ y lx ly hx0box htri0 hydata hyinj hlxf hlyf hsingle)
    (fcc_rootedSingleCutSeparation_of_claw ω n x₀ y lx ly hx0box htri0 hydata hyinj hlyf hGstar
      hsingle b hbdata hcy hcx hcentral)

end Percolation

end StatMech
