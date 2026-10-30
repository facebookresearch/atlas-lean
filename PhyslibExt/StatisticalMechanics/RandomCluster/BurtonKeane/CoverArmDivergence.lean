/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoxSurfaceVolume
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Probability.Percolation.InfiniteClusterCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneUniqueness
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneMerge
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmEndsDistinct
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestLeafInjectionBound
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SingleCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PrivateArmTwoTrif
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestPeel
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.HallArmEnds
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmEndDisjoint
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DivergentArmOrder
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClawDivergentArmOrder
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PairwiseCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.DirectionalDivergence
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootedTreeArmSelection
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootedColoredForest
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootedSpanningForest
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootedSingleCutSeparation

/-!
# Rooted arm divergence and the three-arm cover

A claw obstructs rooted private arms, rooted arm divergence gives rooted single-cut separation, and
with the three-arm cover it gives the rooted spanning forest and the trifurcation count.

## i. Overview

If a trifurcation `x₀` is connected to trifurcations in each of its three arms, every choice of arm
end for `x₀` is reached by one of them, which obstructs rooted private arms (`rfp_ClawArmGeometry`).
A path on `ℤ¹` shows the arm clauses are consistent. `rfp_RootedArmDivergence ω n` asks for arm ends
and a rank such that for connected trifurcations the end of the lower one is cut off by removing the
higher one. It gives rooted single-cut separation and, with the three-arm cover `fcc_ThreeArmCover`,
the rooted spanning forest and the count bound. It holds with no trifurcation, two trifurcations, or
a claw.

The configuration-wide form of these conditions, for every configuration and every box of radius
`n ≥ 1`, is unsatisfiable when `d ≥ 1`: it implies `Tcount d ω n ≤ boxSV_boundaryCard d n` for every
configuration, which `tfc_not_forall_Tcount_le_boundary` refutes
(`rfp_not_forall_coverArmDivergence`). The Burton–Keane theorems that assumed them were removed as
vacuous.

## ii. Key results

- `rfp_not_rootedPrivateArm_of_clawArmGeometry` : a claw obstructs rooted private arms.
- `rfp_Tcount_le_boundary_of_coverArmDivergence` : the count bound from the cover and divergence.

## iii. Table of contents

- A. The root arm obstruction
- B. A path on ℤ¹
- C. Claws
- D. Rooted arm divergence
- E. Unsatisfiability of the configuration-wide conditions

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}

/-! ## A. The root arm obstruction -/

lemma rfp_root_arm_obstruction (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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
  · obtain ⟨hfar, _hpriv⟩ := hpair x₀ hx0box htri0 z hzbox htriz hne hconn hlt
    exact hcrossed hfar
  · exact hrank heq
  · obtain ⟨_hfar, hpriv⟩ :=
      hpair z hzbox htriz x₀ hx0box htri0 hne.symm hconn.symm hgt
    exact hpriv hbeyond

/-! ## B. A path on ℤ¹ -/

/-- The site `0` of `ℤ¹`. -/
noncomputable def rfp_p0 : Site 1 := fun _ => 0

/-- The site `1` of `ℤ¹`. -/
noncomputable def rfp_p1 : Site 1 := fun _ => 1

/-- The site `2` of `ℤ¹`. -/
noncomputable def rfp_p2 : Site 1 := fun _ => 2

/-- The configuration on `ℤ¹` with open edges `0 — 1` and `1 — 2`. -/
noncomputable def rfp_ωpath : ConfigSpace (Sym2 (Site 1)) :=
  fun e => decide (e = s(rfp_p0, rfp_p1) ∨ e = s(rfp_p1, rfp_p2))

lemma rfp_consistency_beyond :
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

lemma rfp_path_noEdge_after_p1 (a b : Site 1) :
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

lemma rfp_path_conn_eq_after_p1 {a b : Site 1}
    (h : Connected 1 (removeSite rfp_p1 rfp_ωpath) a b) : a = b := by
  obtain ⟨w⟩ := h
  cases w with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (rfp_path_noEdge_after_p1 _ _)

lemma rfp_consistency_crossed :
    ¬ Connected 1 (removeSite rfp_p1 rfp_ωpath) rfp_p2 rfp_p0 := by
  intro h
  have heq := rfp_path_conn_eq_after_p1 h
  have := congrFun heq ⟨0, by norm_num⟩
  simp [rfp_p0, rfp_p2] at this

lemma rfp_armGeometry_consistent :
    ∃ (ω : ConfigSpace (Sym2 (Site 1))) (x₀ z w : Site 1),
      Connected 1 (removeSite x₀ ω) w z ∧ ¬ Connected 1 (removeSite z ω) w x₀ :=
  ⟨rfp_ωpath, rfp_p0, rfp_p1, rfp_p2, rfp_consistency_beyond, rfp_consistency_crossed⟩

/-! ## C. Claws -/

/-- Claw arm geometry: some trifurcation `x₀` of the box such that every arm end for `x₀` is
reached,
after removing `x₀`, by a trifurcation connected to `x₀`. -/
def rfp_ClawArmGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ x₀ : Site d, x₀ ∈ box d n ∧ IsTrifurcation d ω x₀ ∧
    ∀ b : Site d → Site d,
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite →
      ∃ z, z ∈ box d n ∧ IsTrifurcation d ω z ∧ x₀ ≠ z ∧ Connected d ω x₀ z ∧
        Connected d (removeSite x₀ ω) (b x₀) z ∧
        ¬ Connected d (removeSite z ω) (b x₀) x₀

lemma rfp_not_rootedPrivateArm_of_clawArmGeometry (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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

lemma rfp_clawArmGeometry_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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

/-! ## D. Rooted arm divergence -/

/-- Rooted arm divergence: arm ends `b x` with infinite clusters outside the trifurcation set and a
rank
separating connected trifurcations, such that removing the higher of two connected trifurcations
cuts its end from the end of the lower one. -/
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

lemma rfp_rootedSingleCutSeparation_of_armDivergence (ω : ConfigSpace (Sym2 (Site d)))
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

lemma rfp_rootedArmDivergence_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    rfp_RootedArmDivergence ω n := by
  refine ⟨id, (fun _ => toLex (0, 0)), ?_, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)

lemma rfp_rootedArmDivergence_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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
      · simp only [ite_eq_right hx0y0, ite_eq_left]; exact stt_lex_ne_fst (by norm_num)
    · rcases htwo x' hx'box htri' with rfl | rfl
      · simp only [ite_eq_right hx0y0, ite_eq_left]; exact stt_lex_ne_fst (by norm_num)
      · exact absurd rfl hxx'
  · intro x hxbox htri x' hx'box htri' hxx' _ hlt
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo x' hx'box htri' with rfl | rfl
      · exact absurd rfl hxx'
      · exact hdeep
    · rcases htwo x' hx'box htri' with rfl | rfl
      · simp only [ite_eq_right hx0y0, ite_eq_left] at hlt
        exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
      · exact absurd rfl hxx'

lemma rfp_rootedArmDivergence_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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

lemma rfp_rootedSpanningForest_of_coverArmDivergence (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hcov : fcc_ThreeArmCover ω n) (hdiv : rfp_RootedArmDivergence ω n) :
    stt_RootedSpanningForest ω n :=
  fcc_rootedSpanningForest_of_coverSep ω n hcov
    (rfp_rootedSingleCutSeparation_of_armDivergence ω n hdiv)

lemma rfp_Tcount_le_boundary_of_coverArmDivergence (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (hcov : fcc_ThreeArmCover ω n) (hdiv : rfp_RootedArmDivergence ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  stt_Tcount_le_boundary_of_rootedSpanningForest ω n hn
    (rfp_rootedSpanningForest_of_coverArmDivergence ω n hcov hdiv)

/-! ## E. Unsatisfiability of the configuration-wide conditions -/

/-- `fcc_ThreeArmCover` and `rfp_RootedArmDivergence` for every configuration and every box of
radius
`n ≥ 1` are impossible when `d ≥ 1`: this implies the configuration-wide bound `Tcount ≤ |∂Λₙ|`,
which `tfc_not_forall_Tcount_le_boundary` refutes. -/
lemma rfp_not_forall_coverArmDivergence (hd : 1 ≤ d) :
    ¬ ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      fcc_ThreeArmCover ω n ∧ rfp_RootedArmDivergence ω n :=
  fun h => tfc_not_forall_Tcount_le_boundary hd fun ω n hn =>
    rfp_Tcount_le_boundary_of_coverArmDivergence ω n hn (h ω n hn).1 (h ω n hn).2

end Percolation

end StatMech
