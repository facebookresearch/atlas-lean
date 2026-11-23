/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Convenient.StdSimplexHornLocus
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedHornLocusPolymorphic
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.RealizedHornHomotopy
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatModelStructure
public import MathlibExt.Topology.Category.TopCat.HomotopyPullback
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberBasepointChange
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatStrictFiberHomotopyFiber
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyProduct
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatRightProper
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Homotopy.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Simplicial Topology
open scoped Simplicial unitInterval

namespace TopCatRealizedHornIntervalPrismRetractionPreflight

private def intervalGaugeReal (r : ℝ) : ℝ :=
  min 1 (min (4 * r) (4 * (1 - r)))

private def intervalCollapseReal (r : ℝ) : ℝ :=
  max 0 (min 1 (2 * r - 1 / 2))

private def intervalSlopeReal (r : ℝ) : ℝ :=
  max (-1 / 4) (min (1 / 4) (r - 1 / 2))

private theorem continuous_intervalGaugeReal : Continuous intervalGaugeReal := by
  unfold intervalGaugeReal
  exact continuous_const.min
    ((continuous_const.mul continuous_id).min
      (continuous_const.mul (continuous_const.sub continuous_id)))

private theorem continuous_intervalCollapseReal :
    Continuous intervalCollapseReal := by
  unfold intervalCollapseReal
  exact continuous_const.max
    (continuous_const.min
      (continuous_const.mul continuous_id |>.sub continuous_const))

private theorem continuous_intervalSlopeReal : Continuous intervalSlopeReal := by
  unfold intervalSlopeReal
  exact continuous_const.max
    (continuous_const.min (continuous_id.sub continuous_const))

private theorem interval_data_left {r : ℝ} (_hr0 : 0 ≤ r)
    (hr : r ≤ 1 / 4) :
    intervalGaugeReal r = 4 * r ∧
      intervalCollapseReal r = 0 ∧ intervalSlopeReal r = -1 / 4 := by
  have hrhalf : r ≤ 1 / 2 := by linarith
  have hinner : 4 * r ≤ 4 * (1 - r) := by linarith
  have hone : 4 * r ≤ 1 := by linarith
  have hlin0 : 2 * r - 1 / 2 ≤ 0 := by linarith
  have hlin1 : 2 * r - 1 / 2 ≤ 1 := by linarith
  have hslope : r - 1 / 2 ≤ -1 / 4 := by linarith
  constructor
  · simp [intervalGaugeReal, min_eq_left hinner, min_eq_right hone]
  constructor
  · unfold intervalCollapseReal
    rw [min_eq_right hlin1, max_eq_left hlin0]
  · have hslope1 : r - 1 / 2 ≤ 1 / 4 := by linarith
    unfold intervalSlopeReal
    rw [min_eq_right hslope1, max_eq_left hslope]

private theorem interval_data_middle {r : ℝ} (hrl : 1 / 4 ≤ r)
    (hrr : r ≤ 3 / 4) :
    intervalGaugeReal r = 1 ∧
      intervalCollapseReal r = 2 * r - 1 / 2 ∧
        intervalSlopeReal r = r - 1 / 2 := by
  have hleft : 1 ≤ 4 * r := by linarith
  have hright : 1 ≤ 4 * (1 - r) := by linarith
  have hinner : 1 ≤ min (4 * r) (4 * (1 - r)) :=
    le_min hleft hright
  have hlin0 : 0 ≤ 2 * r - 1 / 2 := by linarith
  have hlin1 : 2 * r - 1 / 2 ≤ 1 := by linarith
  have hslope0 : -1 / 4 ≤ r - 1 / 2 := by linarith
  have hslope1 : r - 1 / 2 ≤ 1 / 4 := by linarith
  constructor
  · simp [intervalGaugeReal, min_eq_left hinner]
  constructor
  · unfold intervalCollapseReal
    rw [min_eq_right hlin1, max_eq_right hlin0]
  · unfold intervalSlopeReal
    rw [min_eq_right hslope1, max_eq_right hslope0]

private theorem interval_data_right {r : ℝ} (hr : 3 / 4 ≤ r)
    (_hr1 : r ≤ 1) :
    intervalGaugeReal r = 4 * (1 - r) ∧
      intervalCollapseReal r = 1 ∧ intervalSlopeReal r = 1 / 4 := by
  have hrhalf : 1 / 2 ≤ r := by linarith
  have hinner : 4 * (1 - r) ≤ 4 * r := by linarith
  have hone : 4 * (1 - r) ≤ 1 := by linarith
  have hlin1 : 1 ≤ 2 * r - 1 / 2 := by linarith
  have hslope : 1 / 4 ≤ r - 1 / 2 := by linarith
  constructor
  · simp [intervalGaugeReal, min_eq_right hinner, min_eq_right hone]
  constructor
  · unfold intervalCollapseReal
    rw [min_eq_left hlin1, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
  · unfold intervalSlopeReal
    rw [min_eq_left hslope,
      max_eq_right (by norm_num : (-1 / 4 : ℝ) ≤ 1 / 4)]

private theorem interval_collapse_identity {r : ℝ} (hr : r ∈ Set.Icc 0 1) :
    intervalCollapseReal r =
      r + intervalGaugeReal r * intervalSlopeReal r := by
  rcases hr with ⟨hr0, hr1⟩
  by_cases hl : r ≤ 1 / 4
  · obtain ⟨hv, hq, hd⟩ := interval_data_left hr0 hl
    rw [hv, hq, hd]
    ring
  · have hl' : 1 / 4 ≤ r := le_of_not_ge hl
    by_cases hu : 3 / 4 ≤ r
    · obtain ⟨hv, hq, hd⟩ := interval_data_right hu hr1
      rw [hv, hq, hd]
      ring
    · have hu' : r ≤ 3 / 4 := le_of_not_ge hu
      obtain ⟨hv, hq, hd⟩ := interval_data_middle hl' hu'
      rw [hv, hq, hd]
      ring

private lemma erase_nonempty {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N) :
    (Finset.univ.erase i).Nonempty := by
  let i₀ : Fin (N + 1) := ⟨0, Nat.succ_pos N⟩
  let i₁ : Fin (N + 1) := ⟨1, by omega⟩
  have h₀₁ : i₀ ≠ i₁ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [i₀, i₁] at hv
    omega
  by_cases hi : i = i₀
  · exact ⟨i₁, Finset.mem_erase.mpr ⟨by simpa [hi] using h₀₁.symm,
        Finset.mem_univ _⟩⟩
  · exact ⟨i₀, Finset.mem_erase.mpr ⟨Ne.symm hi, Finset.mem_univ _⟩⟩

private noncomputable def hornDepth {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N)
    (x : Convexity.StdSimplex ℝ (Fin (N + 1))) : ℝ :=
  (Finset.univ.erase i).inf' (erase_nonempty i hN) (fun j => x.weights j)

private theorem hornDepth_nonneg {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N)
    (x : Convexity.StdSimplex ℝ (Fin (N + 1))) : 0 ≤ hornDepth i hN x := by
  unfold hornDepth
  rw [Finset.le_inf'_iff]
  intro j _
  exact x.weights_nonneg j

private theorem hornDepth_le {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N)
    (x : Convexity.StdSimplex ℝ (Fin (N + 1))) (j : Fin (N + 1))
    (hji : j ≠ i) : hornDepth i hN x ≤ x.weights j := by
  unfold hornDepth
  exact Finset.inf'_le _ (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)

private theorem hornDepth_le_one {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N)
    (x : Convexity.StdSimplex ℝ (Fin (N + 1))) : hornDepth i hN x ≤ 1 := by
  obtain ⟨j, hj⟩ := erase_nonempty i hN
  exact (hornDepth_le i hN x j (Finset.mem_erase.mp hj).1).trans
    (Convexity.StdSimplex.weights_apply_le_one x j)

private theorem continuous_hornDepth {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N) :
    Continuous (hornDepth i hN) := by
  unfold hornDepth
  exact Continuous.finset_inf'_apply _
    (fun j _ => Convexity.StdSimplex.continuous_weights_apply (R := ℝ) j)

private theorem hornDepth_eq_zero_iff {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N)
    (x : Convexity.StdSimplex ℝ (Fin (N + 1))) :
    hornDepth i hN x = 0 ↔ ∃ j, j ≠ i ∧ x.weights j = 0 := by
  constructor
  · intro hzero
    obtain ⟨j, hjmem, hjmin⟩ := Finset.exists_min_image
      (Finset.univ.erase i) (fun j => x.weights j) (erase_nonempty i hN)
    have hji : j ≠ i := (Finset.mem_erase.mp hjmem).1
    have hle : hornDepth i hN x ≤ x.weights j := hornDepth_le i hN x j hji
    have hjle : x.weights j ≤ hornDepth i hN x := by
      unfold hornDepth
      rw [Finset.le_inf'_iff]
      intro k hk
      exact hjmin k hk
    exact ⟨j, hji, by linarith⟩
  · rintro ⟨j, hji, hjzero⟩
    have hle := hornDepth_le i hN x j hji
    have hnonneg := hornDepth_nonneg i hN x
    linarith

private noncomputable def hornShift {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N)
    (x : Convexity.StdSimplex ℝ (Fin (N + 1))) (c : ℝ)
    (hc0 : 0 ≤ c) (hca : c ≤ hornDepth i hN x) :
    Convexity.StdSimplex ℝ (Fin (N + 1)) where
  weights := Finsupp.equivFunOnFinite.symm (fun j =>
    if j = i then x.weights i + (N : ℝ) * c else x.weights j - c)
  nonneg j := by
    by_cases hji : j = i
    · subst j
      simp only [Finsupp.coe_equivFunOnFinite_symm, ite_true]
      exact add_nonneg (x.weights_nonneg i)
        (mul_nonneg (Nat.cast_nonneg N) hc0)
    · simp only [Finsupp.coe_equivFunOnFinite_symm, hji, ite_false]
      exact sub_nonneg.mpr (hca.trans (hornDepth_le i hN x j hji))
  total := by
    have hcard : (Finset.univ.erase i).card = N := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
      simp [Fintype.card_fin]
    have hsplit : ∑ j, (if j = i then x.weights i + (N : ℝ) * c
        else x.weights j - c) =
      (x.weights i + (N : ℝ) * c) +
        ∑ j ∈ Finset.univ.erase i, (x.weights j - c) := by
      rw [← Finset.add_sum_erase Finset.univ
        (fun j => if j = i then x.weights i + (N : ℝ) * c
          else x.weights j - c) (Finset.mem_univ i)]
      simp only [ite_true]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      simp [(Finset.mem_erase.mp hj).1]
    rw [Finsupp.equivFunOnFinite_symm_sum, hsplit, Finset.sum_sub_distrib]
    have hconst : ∑ _j ∈ Finset.univ.erase i, c = (N : ℝ) * c := by
      rw [Finset.sum_const, hcard, nsmul_eq_mul]
    rw [hconst]
    have htotal := x.total_of_fintype
    have hsplitx : ∑ j, x.weights j =
        x.weights i + ∑ j ∈ Finset.univ.erase i, x.weights j :=
      (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)).symm
    linarith

@[simp] private theorem hornShift_apply {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N)
    (x : Convexity.StdSimplex ℝ (Fin (N + 1))) (c : ℝ)
    (hc0 : 0 ≤ c) (hca : c ≤ hornDepth i hN x) (j : Fin (N + 1)) :
    (hornShift i hN x c hc0 hca).weights j =
      if j = i then x.weights i + (N : ℝ) * c else x.weights j - c := rfl

private theorem hornShift_zero {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N)
    (x : Convexity.StdSimplex ℝ (Fin (N + 1))) :
    hornShift i hN x 0 (le_refl 0) (hornDepth_nonneg i hN x) = x := by
  apply Convexity.StdSimplex.ext
  ext j
  by_cases hji : j = i
  · simp [hornShift_apply, hji]
  · simp [hornShift_apply, hji]

private theorem hornShift_depth_horn {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N)
    (x : Convexity.StdSimplex ℝ (Fin (N + 1))) :
    hornShift i hN x (hornDepth i hN x) (hornDepth_nonneg i hN x) le_rfl ∈
      hornLocus i hN := by
  rw [hornLocus]
  obtain ⟨j, hjmem, hjmin⟩ := Finset.exists_min_image
    (Finset.univ.erase i) (fun j => x.weights j) (erase_nonempty i hN)
  have hji : j ≠ i := (Finset.mem_erase.mp hjmem).1
  have hle := hornDepth_le i hN x j hji
  have hjle : x.weights j ≤ hornDepth i hN x := by
    unfold hornDepth
    rw [Finset.le_inf'_iff]
    intro k hk
    exact hjmin k hk
  exact ⟨j, hji, by simp [hornShift_apply, hji, le_antisymm hjle hle]⟩

private def hornGauge {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N)
    (x : Convexity.StdSimplex ℝ (Fin (N + 1))) : ℝ :=
  hornDepth i hN x / 2

private theorem hornGauge_nonneg {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N)
    (x : Convexity.StdSimplex ℝ (Fin (N + 1))) : 0 ≤ hornGauge i hN x := by
  exact div_nonneg (hornDepth_nonneg i hN x) (by norm_num)

private theorem hornGauge_le_half {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N)
    (x : Convexity.StdSimplex ℝ (Fin (N + 1))) : hornGauge i hN x ≤ 1 / 2 := by
  unfold hornGauge
  linarith [hornDepth_le_one i hN x]

private theorem continuous_hornGauge {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N) :
    Continuous (hornGauge i hN) := by
  exact (continuous_hornDepth i hN).div_const 2

private def intervalGauge (t : unitInterval) : ℝ :=
  intervalGaugeReal t

private theorem intervalGauge_nonneg (t : unitInterval) : 0 ≤ intervalGauge t := by
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  unfold intervalGauge intervalGaugeReal
  apply le_min (by norm_num)
  exact le_min (mul_nonneg (by norm_num) ht0)
    (mul_nonneg (by norm_num) (sub_nonneg.mpr ht1))

private theorem intervalGauge_le_one (t : unitInterval) : intervalGauge t ≤ 1 := by
  exact min_le_left _ _

private theorem continuous_intervalGauge : Continuous intervalGauge :=
  continuous_intervalGaugeReal.comp continuous_subtype_val

private def intervalCollapse (t : unitInterval) : unitInterval :=
  ⟨intervalCollapseReal t,
    ⟨le_max_left _ _,
      max_le (by norm_num) (min_le_left _ _)⟩⟩

private theorem continuous_intervalCollapse : Continuous intervalCollapse := by
  apply Continuous.subtype_mk
  exact continuous_intervalCollapseReal.comp continuous_subtype_val

private def intervalSlope (t : unitInterval) : ℝ :=
  intervalSlopeReal t

private theorem continuous_intervalSlope : Continuous intervalSlope :=
  continuous_intervalSlopeReal.comp continuous_subtype_val

private theorem intervalCollapse_identity (t : unitInterval) :
    (intervalCollapse t : ℝ) =
      t + intervalGauge t * intervalSlope t := by
  exact interval_collapse_identity t.2

private theorem intervalCollapse_endpoint_of_gauge_lt_one (t : unitInterval)
    (hv : intervalGauge t < 1) : intervalCollapse t = 0 ∨ intervalCollapse t = 1 := by
  by_cases hl : (t : ℝ) ≤ 1 / 4
  · left
    apply Subtype.ext
    exact (interval_data_left t.2.1 hl).2.1
  · have hl' : 1 / 4 ≤ (t : ℝ) := le_of_not_ge hl
    by_cases hr : 3 / 4 ≤ (t : ℝ)
    · right
      apply Subtype.ext
      exact (interval_data_right hr t.2.2).2.1
    · have hr' : (t : ℝ) ≤ 3 / 4 := le_of_not_ge hr
      have hmid := (interval_data_middle hl' hr').1
      change intervalGaugeReal t < 1 at hv
      rw [hmid] at hv
      exact (lt_irrefl 1 hv).elim

private def hornDominantTimeReal {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N)
    (z : Convexity.StdSimplex ℝ (Fin (N + 1)) × unitInterval) : ℝ :=
  z.2 + hornGauge i hN z.1 * intervalSlope z.2

private theorem continuous_hornDominantTimeReal {N : ℕ}
    (i : Fin (N + 1)) (hN : 0 < N) :
    Continuous (hornDominantTimeReal i hN) := by
  exact (continuous_subtype_val.comp continuous_snd).add
    ((continuous_hornGauge i hN).comp continuous_fst |>.mul
      (continuous_intervalSlope.comp continuous_snd))

private theorem hornDominantTime_mem {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N)
    (z : Convexity.StdSimplex ℝ (Fin (N + 1)) × unitInterval)
    (huv : hornGauge i hN z.1 ≤ intervalGauge z.2) :
    hornDominantTimeReal i hN z ∈ Set.Icc (0 : ℝ) 1 := by
  let r : ℝ := z.2
  have hr0 : 0 ≤ r := z.2.2.1
  have hr1 : r ≤ 1 := z.2.2.2
  have hu0 := hornGauge_nonneg i hN z.1
  by_cases hl : r ≤ 1 / 4
  · obtain ⟨hv, _, hd⟩ := interval_data_left hr0 hl
    change 0 ≤ r + hornGauge i hN z.1 * intervalSlopeReal r ∧
      r + hornGauge i hN z.1 * intervalSlopeReal r ≤ 1
    rw [hd]
    change hornGauge i hN z.1 ≤ intervalGaugeReal r at huv
    rw [hv] at huv
    constructor <;> nlinarith
  · have hl' : 1 / 4 ≤ r := le_of_not_ge hl
    by_cases hr : 3 / 4 ≤ r
    · obtain ⟨hv, _, hd⟩ := interval_data_right hr hr1
      change 0 ≤ r + hornGauge i hN z.1 * intervalSlopeReal r ∧
        r + hornGauge i hN z.1 * intervalSlopeReal r ≤ 1
      rw [hd]
      change hornGauge i hN z.1 ≤ intervalGaugeReal r at huv
      rw [hv] at huv
      constructor <;> nlinarith
    · have hr' : r ≤ 3 / 4 := le_of_not_ge hr
      obtain ⟨_, hq, hd⟩ := interval_data_middle hl' hr'
      have hu1 : hornGauge i hN z.1 ≤ 1 :=
        (hornGauge_le_half i hN z.1).trans (by norm_num)
      have hq0 : 0 ≤ 2 * r - 1 / 2 := by linarith
      have hq1 : 2 * r - 1 / 2 ≤ 1 := by linarith
      have hleft : 0 ≤ (1 - hornGauge i hN z.1) * r :=
        mul_nonneg (sub_nonneg.mpr hu1) hr0
      have hright : 0 ≤ hornGauge i hN z.1 * (2 * r - 1 / 2) :=
        mul_nonneg hu0 hq0
      have hleft' : 0 ≤ (1 - hornGauge i hN z.1) * (1 - r) :=
        mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr hr1)
      have hright' : 0 ≤ hornGauge i hN z.1 * (1 - (2 * r - 1 / 2)) :=
        mul_nonneg hu0 (sub_nonneg.mpr hq1)
      change 0 ≤ r + hornGauge i hN z.1 * intervalSlopeReal r ∧
        r + hornGauge i hN z.1 * intervalSlopeReal r ≤ 1
      rw [hd]
      constructor <;> nlinarith

private def fullShiftCoord {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N)
    (j : Fin (N + 1))
    (z : Convexity.StdSimplex ℝ (Fin (N + 1)) × unitInterval) : ℝ :=
  if j = i then z.1.weights i + (N : ℝ) * hornDepth i hN z.1
  else z.1.weights j - hornDepth i hN z.1

private def partialShiftCoord {N : ℕ} (i : Fin (N + 1))
    (j : Fin (N + 1))
    (z : Convexity.StdSimplex ℝ (Fin (N + 1)) × unitInterval) : ℝ :=
  if j = i then z.1.weights i + (N : ℝ) * (2 * intervalGauge z.2)
  else z.1.weights j - 2 * intervalGauge z.2

private theorem continuous_fullShiftCoord {N : ℕ} (i : Fin (N + 1))
    (hN : 0 < N) (j : Fin (N + 1)) : Continuous (fullShiftCoord i hN j) := by
  unfold fullShiftCoord
  let Z := Convexity.StdSimplex ℝ (Fin (N + 1)) × unitInterval
  have hNconst : Continuous (fun _ : Z => (N : ℝ)) := continuous_const
  have hDepth : Continuous (fun z : Z => hornDepth i hN z.1) :=
    (continuous_hornDepth i hN).comp continuous_fst
  by_cases hji : j = i
  · simp only [hji, ite_true]
    exact ((Convexity.StdSimplex.continuous_weights_apply (R := ℝ) i).comp
      continuous_fst).add (hNconst.mul hDepth)
  · simp only [hji, ite_false]
    exact ((Convexity.StdSimplex.continuous_weights_apply (R := ℝ) j).comp
      continuous_fst).sub hDepth

private theorem continuous_partialShiftCoord {N : ℕ} (i : Fin (N + 1))
    (j : Fin (N + 1)) : Continuous (partialShiftCoord i j) := by
  unfold partialShiftCoord
  let Z := Convexity.StdSimplex ℝ (Fin (N + 1)) × unitInterval
  have hNconst : Continuous (fun _ : Z => (N : ℝ)) := continuous_const
  have hTwo : Continuous (fun _ : Z => (2 : ℝ)) := continuous_const
  have hGauge : Continuous (fun z : Z => intervalGauge z.2) :=
    continuous_intervalGauge.comp continuous_snd
  by_cases hji : j = i
  · simp only [hji, ite_true]
    exact ((Convexity.StdSimplex.continuous_weights_apply (R := ℝ) i).comp
      continuous_fst).add (hNconst.mul (hTwo.mul hGauge))
  · simp only [hji, ite_false]
    exact ((Convexity.StdSimplex.continuous_weights_apply (R := ℝ) j).comp
      continuous_fst).sub (hTwo.mul hGauge)

private noncomputable def prismSimplex {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N)
    (z : Convexity.StdSimplex ℝ (Fin (N + 1)) × unitInterval) :
    Convexity.StdSimplex ℝ (Fin (N + 1)) := by
  by_cases h : hornGauge i hN z.1 ≤ intervalGauge z.2
  · exact hornShift i hN z.1 (hornDepth i hN z.1)
      (hornDepth_nonneg i hN z.1) le_rfl
  · have hv0 := intervalGauge_nonneg z.2
    have hvu : intervalGauge z.2 < hornGauge i hN z.1 := lt_of_not_ge h
    exact hornShift i hN z.1 (2 * intervalGauge z.2)
      (mul_nonneg (by norm_num) hv0) (by
        unfold hornGauge at hvu
        linarith)

private theorem prismSimplex_weights {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N)
    (z : Convexity.StdSimplex ℝ (Fin (N + 1)) × unitInterval)
    (j : Fin (N + 1)) :
    (prismSimplex i hN z).weights j =
      if hornGauge i hN z.1 ≤ intervalGauge z.2
      then fullShiftCoord i hN j z else partialShiftCoord i j z := by
  unfold prismSimplex
  split <;> rfl

private theorem continuous_prismSimplex {N : ℕ} (i : Fin (N + 1))
    (hN : 0 < N) : Continuous (prismSimplex i hN) := by
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ
    (Fin (N + 1))).continuous_iff.mpr
  rw [continuous_pi_iff]
  intro j
  change Continuous (fun z => (prismSimplex i hN z).weights j)
  simp only [prismSimplex_weights]
  apply Continuous.if_le
    (continuous_fullShiftCoord i hN j)
    (continuous_partialShiftCoord i j)
    ((continuous_hornGauge i hN).comp continuous_fst)
    (continuous_intervalGauge.comp continuous_snd)
  intro z huv
  change hornGauge i hN z.1 = intervalGauge z.2 at huv
  by_cases hji : j = i
  · simp only [fullShiftCoord, partialShiftCoord, hji, ite_true]
    congr 1
    unfold hornGauge at huv
    nlinarith
  · simp only [fullShiftCoord, partialShiftCoord, hji, ite_false]
    unfold hornGauge at huv
    nlinarith

private def prismTimeReal {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N)
    (z : Convexity.StdSimplex ℝ (Fin (N + 1)) × unitInterval) : ℝ :=
  if hornGauge i hN z.1 ≤ intervalGauge z.2
  then hornDominantTimeReal i hN z else intervalCollapseReal z.2

private theorem prismTimeReal_mem {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N)
    (z : Convexity.StdSimplex ℝ (Fin (N + 1)) × unitInterval) :
    prismTimeReal i hN z ∈ Set.Icc (0 : ℝ) 1 := by
  unfold prismTimeReal
  split
  · exact hornDominantTime_mem i hN z ‹_›
  · exact (intervalCollapse z.2).2

private theorem continuous_prismTimeReal {N : ℕ} (i : Fin (N + 1))
    (hN : 0 < N) : Continuous (prismTimeReal i hN) := by
  unfold prismTimeReal
  apply Continuous.if_le
    (continuous_hornDominantTimeReal i hN)
    (continuous_intervalCollapseReal.comp
      (continuous_subtype_val.comp continuous_snd))
    ((continuous_hornGauge i hN).comp continuous_fst)
    (continuous_intervalGauge.comp continuous_snd)
  intro z huv
  change hornGauge i hN z.1 = intervalGaugeReal z.2 at huv
  change hornDominantTimeReal i hN z = intervalCollapseReal z.2
  rw [interval_collapse_identity z.2.2]
  change (z.2 : ℝ) + hornGauge i hN z.1 * intervalSlopeReal z.2 =
    (z.2 : ℝ) + intervalGaugeReal z.2 * intervalSlopeReal z.2
  rw [huv]

private def prismTime {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N)
    (z : Convexity.StdSimplex ℝ (Fin (N + 1)) × unitInterval) :
    unitInterval :=
  ⟨prismTimeReal i hN z, prismTimeReal_mem i hN z⟩

private theorem continuous_prismTime {N : ℕ} (i : Fin (N + 1))
    (hN : 0 < N) : Continuous (prismTime i hN) := by
  apply Continuous.subtype_mk
  exact continuous_prismTimeReal i hN

private theorem prismSimplex_of_hornDominant {N : ℕ} (i : Fin (N + 1))
    (hN : 0 < N)
    (z : Convexity.StdSimplex ℝ (Fin (N + 1)) × unitInterval)
    (h : hornGauge i hN z.1 ≤ intervalGauge z.2) :
    prismSimplex i hN z =
      hornShift i hN z.1 (hornDepth i hN z.1)
        (hornDepth_nonneg i hN z.1) le_rfl := by
  unfold prismSimplex
  simp only [h, dite_true]

private theorem prismSimplex_of_intervalDominant {N : ℕ} (i : Fin (N + 1))
    (hN : 0 < N)
    (z : Convexity.StdSimplex ℝ (Fin (N + 1)) × unitInterval)
    (h : ¬ hornGauge i hN z.1 ≤ intervalGauge z.2) :
    prismSimplex i hN z =
      hornShift i hN z.1 (2 * intervalGauge z.2)
        (mul_nonneg (by norm_num) (intervalGauge_nonneg z.2)) (by
          have hvu : intervalGauge z.2 < hornGauge i hN z.1 := lt_of_not_ge h
          unfold hornGauge at hvu
          linarith) := by
  unfold prismSimplex
  simp only [h, dite_false]

private theorem prismTime_of_hornDominant {N : ℕ} (i : Fin (N + 1))
    (hN : 0 < N)
    (z : Convexity.StdSimplex ℝ (Fin (N + 1)) × unitInterval)
    (h : hornGauge i hN z.1 ≤ intervalGauge z.2) :
    prismTime i hN z =
      ⟨hornDominantTimeReal i hN z, hornDominantTime_mem i hN z h⟩ := by
  apply Subtype.ext
  simp [prismTime, prismTimeReal, h]

private theorem prismTime_of_intervalDominant {N : ℕ} (i : Fin (N + 1))
    (hN : 0 < N)
    (z : Convexity.StdSimplex ℝ (Fin (N + 1)) × unitInterval)
    (h : ¬ hornGauge i hN z.1 ≤ intervalGauge z.2) :
    prismTime i hN z = intervalCollapse z.2 := by
  apply Subtype.ext
  simp [prismTime, prismTimeReal, intervalCollapse, h]

private theorem prismSimplex_mem_horn_of_hornDominant {N : ℕ}
    (i : Fin (N + 1)) (hN : 0 < N)
    (z : Convexity.StdSimplex ℝ (Fin (N + 1)) × unitInterval)
    (h : hornGauge i hN z.1 ≤ intervalGauge z.2) :
    prismSimplex i hN z ∈ hornLocus i hN := by
  rw [prismSimplex_of_hornDominant i hN z h]
  exact hornShift_depth_horn i hN z.1

private theorem prismTime_endpoint_of_intervalDominant {N : ℕ}
    (i : Fin (N + 1)) (hN : 0 < N)
    (z : Convexity.StdSimplex ℝ (Fin (N + 1)) × unitInterval)
    (h : ¬ hornGauge i hN z.1 ≤ intervalGauge z.2) :
    prismTime i hN z = 0 ∨ prismTime i hN z = 1 := by
  rw [prismTime_of_intervalDominant i hN z h]
  apply intervalCollapse_endpoint_of_gauge_lt_one
  have hvu : intervalGauge z.2 < hornGauge i hN z.1 := lt_of_not_ge h
  calc
    intervalGauge z.2 < hornGauge i hN z.1 := hvu
    _ ≤ 1 / 2 := hornGauge_le_half i hN z.1
    _ < 1 := by norm_num

private abbrev AffinePrismBoundary {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N) :=
  {z : Convexity.StdSimplex ℝ (Fin (N + 1)) × unitInterval //
    z.1 ∈ hornLocus i hN ∨ z.2 = 0 ∨ z.2 = 1}

private def affinePrismRetract {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N) :
    ContinuousMap
      (Convexity.StdSimplex ℝ (Fin (N + 1)) × unitInterval)
      (AffinePrismBoundary i hN) where
  toFun z := ⟨(prismSimplex i hN z, prismTime i hN z), by
    by_cases h : hornGauge i hN z.1 ≤ intervalGauge z.2
    · exact Or.inl (prismSimplex_mem_horn_of_hornDominant i hN z h)
    · exact Or.inr (prismTime_endpoint_of_intervalDominant i hN z h)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_prismSimplex i hN).prodMk (continuous_prismTime i hN)

private theorem prismSimplex_fix_horn {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N)
    (z : Convexity.StdSimplex ℝ (Fin (N + 1)) × unitInterval)
    (hz : z.1 ∈ hornLocus i hN) : prismSimplex i hN z = z.1 := by
  have ha : hornDepth i hN z.1 = 0 := (hornDepth_eq_zero_iff i hN z.1).2 hz
  have hu : hornGauge i hN z.1 = 0 := by simp [hornGauge, ha]
  have hdom : hornGauge i hN z.1 ≤ intervalGauge z.2 := by
    rw [hu]
    exact intervalGauge_nonneg z.2
  rw [prismSimplex_of_hornDominant i hN z hdom]
  simpa [ha] using hornShift_zero i hN z.1

private theorem prismTime_fix_horn {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N)
    (z : Convexity.StdSimplex ℝ (Fin (N + 1)) × unitInterval)
    (hz : z.1 ∈ hornLocus i hN) : prismTime i hN z = z.2 := by
  have ha : hornDepth i hN z.1 = 0 := (hornDepth_eq_zero_iff i hN z.1).2 hz
  have hu : hornGauge i hN z.1 = 0 := by simp [hornGauge, ha]
  have hdom : hornGauge i hN z.1 ≤ intervalGauge z.2 := by
    rw [hu]
    exact intervalGauge_nonneg z.2
  rw [prismTime_of_hornDominant i hN z hdom]
  apply Subtype.ext
  simp [hornDominantTimeReal, hu]

private theorem intervalGauge_eq_zero_of_endpoint (t : unitInterval)
    (ht : t = 0 ∨ t = 1) : intervalGauge t = 0 := by
  rcases ht with rfl | rfl <;> norm_num [intervalGauge, intervalGaugeReal]

private theorem intervalCollapse_fix_endpoint (t : unitInterval)
    (ht : t = 0 ∨ t = 1) : intervalCollapse t = t := by
  rcases ht with rfl | rfl <;> apply Subtype.ext <;>
    norm_num [intervalCollapse, intervalCollapseReal]

private theorem prismSimplex_fix_endpoint {N : ℕ} (i : Fin (N + 1))
    (hN : 0 < N)
    (z : Convexity.StdSimplex ℝ (Fin (N + 1)) × unitInterval)
    (hz : z.2 = 0 ∨ z.2 = 1) : prismSimplex i hN z = z.1 := by
  have hv : intervalGauge z.2 = 0 := intervalGauge_eq_zero_of_endpoint z.2 hz
  by_cases hdom : hornGauge i hN z.1 ≤ intervalGauge z.2
  · have hu0 := hornGauge_nonneg i hN z.1
    have hu : hornGauge i hN z.1 = 0 := by linarith
    have ha : hornDepth i hN z.1 = 0 := by unfold hornGauge at hu; linarith
    rw [prismSimplex_of_hornDominant i hN z hdom]
    simpa [ha] using hornShift_zero i hN z.1
  · rw [prismSimplex_of_intervalDominant i hN z hdom]
    simpa [hv] using hornShift_zero i hN z.1

private theorem prismTime_fix_endpoint {N : ℕ} (i : Fin (N + 1))
    (hN : 0 < N)
    (z : Convexity.StdSimplex ℝ (Fin (N + 1)) × unitInterval)
    (hz : z.2 = 0 ∨ z.2 = 1) : prismTime i hN z = z.2 := by
  have hv : intervalGauge z.2 = 0 := intervalGauge_eq_zero_of_endpoint z.2 hz
  by_cases hdom : hornGauge i hN z.1 ≤ intervalGauge z.2
  · have hu0 := hornGauge_nonneg i hN z.1
    have hu : hornGauge i hN z.1 = 0 := by linarith
    rw [prismTime_of_hornDominant i hN z hdom]
    apply Subtype.ext
    simp [hornDominantTimeReal, hu]
  · rw [prismTime_of_intervalDominant i hN z hdom]
    exact intervalCollapse_fix_endpoint z.2 hz

private theorem affinePrismRetract_fix {N : ℕ} (i : Fin (N + 1)) (hN : 0 < N)
    (z : AffinePrismBoundary i hN) : affinePrismRetract i hN z.1 = z := by
  apply Subtype.ext
  apply Prod.ext
  · rcases z.2 with hz | hz
    · exact prismSimplex_fix_horn i hN z.1 hz
    · exact prismSimplex_fix_endpoint i hN z.1 hz
  · rcases z.2 with hz | hz
    · exact prismTime_fix_horn i hN z.1 hz
    · exact prismTime_fix_endpoint i hN z.1 hz

universe u

private abbrev realizedSimplex (N : ℕ) : Type u :=
  SSet.toTop.obj (Δ[N] : SSet.{u})

private abbrev realizedHorn (N : ℕ) (i : Fin (N + 1)) : Type u :=
  SSet.toTop.obj (SSet.horn.{u} N i)

private def hornInclusion (N : ℕ) (i : Fin (N + 1)) :
    C(realizedHorn.{u} N i, realizedSimplex.{u} N) :=
  (SSet.toTop.map (SSet.horn.{u} N i).ι).hom

private abbrev PrismBoundary (n : ℕ) (i : Fin (n + 2)) :=
  {z : realizedSimplex.{u} (n + 1) × unitInterval //
    z.1 ∈ Set.range (hornInclusion.{u} (n + 1) i) ∨ z.2 = 0 ∨ z.2 = 1}

private noncomputable def realizedToAffinePrism (n : ℕ) :
    ContinuousMap
      (realizedSimplex.{u} (n + 1) × unitInterval)
      (Convexity.StdSimplex ℝ (Fin (n + 2)) × unitInterval) where
  toFun z :=
    (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1)) z.1, z.2)
  continuous_toFun :=
    ((SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))).continuous.comp
      continuous_fst).prodMk continuous_snd

private theorem affineHorn_to_realizedRange (n : ℕ) (i : Fin (n + 2))
    (x : Convexity.StdSimplex ℝ (Fin (n + 2))) (hx : x ∈ hornLocus i (by omega)) :
    (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))).symm x ∈
      Set.range (hornInclusion.{u} (n + 1) i) := by
  have hEq :
      (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))) ''
          Set.range (SSet.toTop.{u}.map (SSet.horn.{u} (n + 1) i).ι) =
        hornLocus i (by omega) := by
    simpa [hornLocus] using
      (hornRange_image_eq_locus_u (n + 1) i (by omega))
  have hx' : x ∈
      (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))) ''
        Set.range (hornInclusion.{u} (n + 1) i) := by
    have hxLocus : x ∈ hornLocus i (by omega) := hx
    rw [← hEq] at hxLocus
    simpa [hornInclusion] using hxLocus
  obtain ⟨y, hy, hyx⟩ := hx'
  obtain ⟨a, rfl⟩ := hy
  refine ⟨a, ?_⟩
  apply (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))).injective
  rw [Homeomorph.apply_symm_apply]
  exact hyx

private theorem realizedRange_to_affineHorn (n : ℕ) (i : Fin (n + 2))
    (x : realizedSimplex.{u} (n + 1))
    (hx : x ∈ Set.range (hornInclusion.{u} (n + 1) i)) :
    SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1)) x ∈
      hornLocus i (by omega) := by
  have hEq :
      (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))) ''
          Set.range (SSet.toTop.{u}.map (SSet.horn.{u} (n + 1) i).ι) =
        hornLocus i (by omega) := by
    simpa [hornLocus] using
      (hornRange_image_eq_locus_u (n + 1) i (by omega))
  have hImage : SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1)) x ∈
      (SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))) ''
        Set.range (SSet.toTop.{u}.map (SSet.horn.{u} (n + 1) i).ι) := by
    exact ⟨x, by simpa [hornInclusion] using hx, rfl⟩
  rw [hEq] at hImage
  simpa [hornLocus] using hImage

private noncomputable def affineBoundaryToRealized (n : ℕ) (i : Fin (n + 2)) :
    ContinuousMap (AffinePrismBoundary i (by omega)) (PrismBoundary.{u} n i) where
  toFun z := ⟨
    ((SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1))).symm z.1.1, z.1.2),
    by
      rcases z.2 with hz | hz
      · exact Or.inl (affineHorn_to_realizedRange n i z.1.1 hz)
      · exact Or.inr hz⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((SimplexCategory.toTopHomeo
      (SimplexCategory.mk (n + 1))).symm.continuous.comp
        (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)

private noncomputable def realizedBoundaryToAffine (n : ℕ) (i : Fin (n + 2)) :
    PrismBoundary.{u} n i → AffinePrismBoundary i (by omega) :=
  fun z => ⟨realizedToAffinePrism n z.1, by
    rcases z.2 with hz | hz
    · exact Or.inl (realizedRange_to_affineHorn n i z.1.1 hz)
    · exact Or.inr hz⟩

private noncomputable def realizedPrismRetract (n : ℕ) (i : Fin (n + 2)) :
    ContinuousMap
      (realizedSimplex.{u} (n + 1) × unitInterval)
      (PrismBoundary.{u} n i) where
  toFun z := affineBoundaryToRealized n i
    (affinePrismRetract i (by omega) (realizedToAffinePrism n z))
  continuous_toFun := (affineBoundaryToRealized n i).continuous.comp
    ((affinePrismRetract i (by omega)).continuous.comp
      (realizedToAffinePrism n).continuous)

private theorem realizedPrismRetract_fix (n : ℕ) (i : Fin (n + 2))
    (z : PrismBoundary.{u} n i) : realizedPrismRetract n i z.1 = z := by
  have hfix := affinePrismRetract_fix i (by omega)
    (realizedBoundaryToAffine n i z)
  apply Subtype.ext
  apply Prod.ext
  · change (SimplexCategory.toTopHomeo
        (SimplexCategory.mk (n + 1))).symm
      (affinePrismRetract i (by omega)
        (realizedToAffinePrism n z.1)).1.1 = z.1.1
    have hfirst := congrArg (fun w => w.1.1) hfix
    change (affinePrismRetract i (by omega)
      (realizedToAffinePrism n z.1)).1.1 =
        SimplexCategory.toTopHomeo (SimplexCategory.mk (n + 1)) z.1.1 at hfirst
    rw [hfirst, Homeomorph.symm_apply_apply]
  · change (affinePrismRetract i (by omega)
      (realizedToAffinePrism n z.1)).1.2 = z.1.2
    exact congrArg (fun w => w.1.2) hfix

end TopCatRealizedHornIntervalPrismRetractionPreflight
namespace TopCatPathEndpointsSelectedFibrationResume

open CategoryTheory.Limits
open TopCatRealizedHornIntervalPrismRetractionPreflight

universe v

private abbrev realizedSimplex (n : ℕ) : Type v :=
  SSet.toTop.obj (Δ[n] : SSet.{v})

private abbrev realizedHorn (n : ℕ) (i : Fin (n + 1)) : Type v :=
  SSet.toTop.obj (SSet.horn.{v} n i)

private def hornInclusion (n : ℕ) (i : Fin (n + 1)) :
    C(realizedHorn.{v} n i, realizedSimplex.{v} n) :=
  (SSet.toTop.map (SSet.horn.{v} n i).ι).hom

private abbrev PrismBoundary (n : ℕ) (i : Fin (n + 2)) :=
  TopCatRealizedHornIntervalPrismRetractionPreflight.PrismBoundary.{v} n i

private def hornSet (n : ℕ) (i : Fin (n + 2)) :
    Set (PrismBoundary.{v} n i) :=
  {z | z.1.1 ∈ Set.range (hornInclusion.{v} (n + 1) i)}

private def zeroSet (n : ℕ) (i : Fin (n + 2)) :
    Set (PrismBoundary.{v} n i) :=
  {z | z.1.2 = 0}

private def oneSet (n : ℕ) (i : Fin (n + 2)) :
    Set (PrismBoundary.{v} n i) :=
  {z | z.1.2 = 1}

private theorem hornSet_isClosed (n : ℕ) (i : Fin (n + 2)) :
    IsClosed (hornSet.{v} n i) := by
  have hj : IsClosedEmbedding (hornInclusion.{v} (n + 1) i) :=
    (TopCat.closedEmbeddings_iff _).mp
      (SSet.horn.closedEmbeddings_toTop_map_ι (n + 1) i)
  exact hj.isClosed_range.preimage
    (continuous_fst.comp continuous_subtype_val)

private theorem zeroSet_isClosed (n : ℕ) (i : Fin (n + 2)) :
    IsClosed (zeroSet.{v} n i) := by
  exact isClosed_singleton.preimage
    (continuous_snd.comp continuous_subtype_val)

private theorem oneSet_isClosed (n : ℕ) (i : Fin (n + 2)) :
    IsClosed (oneSet.{v} n i) := by
  exact isClosed_singleton.preimage
    (continuous_snd.comp continuous_subtype_val)

private def hornFormula (n : ℕ) (i : Fin (n + 2)) (B : TopCat.{v})
    (a : SSet.toTop.obj (SSet.horn.{v} (n + 1) i) ⟶ TopCat.pathObject B)
    (z : PrismBoundary.{v} n i) : B :=
  a (SSet.realizedHornRetract (n + 1) i (by omega) z.1.1)
    (TopCat.I.homeomorph.symm z.1.2)

private theorem continuous_hornFormula (n : ℕ) (i : Fin (n + 2))
    (B : TopCat.{v})
    (a : SSet.toTop.obj (SSet.horn.{v} (n + 1) i) ⟶ TopCat.pathObject B) :
    Continuous (hornFormula n i B a) := by
  exact a.hom.uncurry.continuous.comp
    (((SSet.realizedHornRetract (n + 1) i (by omega)).continuous.comp
      (continuous_fst.comp continuous_subtype_val)).prodMk
        (TopCat.I.homeomorph.symm.continuous.comp
          (continuous_snd.comp continuous_subtype_val)))

private def zeroFormula (n : ℕ) (i : Fin (n + 2)) (B : TopCat.{v})
    (c : SSet.toTop.obj (Δ[n + 1] : SSet.{v}) ⟶ B ⨯ B)
    (z : PrismBoundary.{v} n i) : B :=
  (c ≫ prod.fst) z.1.1

private theorem continuous_zeroFormula (n : ℕ) (i : Fin (n + 2))
    (B : TopCat.{v}) (c : SSet.toTop.obj (Δ[n + 1] : SSet.{v}) ⟶ B ⨯ B) :
    Continuous (zeroFormula n i B c) :=
  (c ≫ prod.fst).hom.continuous.comp
    (continuous_fst.comp continuous_subtype_val)

private def oneFormula (n : ℕ) (i : Fin (n + 2)) (B : TopCat.{v})
    (c : SSet.toTop.obj (Δ[n + 1] : SSet.{v}) ⟶ B ⨯ B)
    (z : PrismBoundary.{v} n i) : B :=
  (c ≫ prod.snd) z.1.1

private theorem continuous_oneFormula (n : ℕ) (i : Fin (n + 2))
    (B : TopCat.{v}) (c : SSet.toTop.obj (Δ[n + 1] : SSet.{v}) ⟶ B ⨯ B) :
    Continuous (oneFormula n i B c) :=
  (c ≫ prod.snd).hom.continuous.comp
    (continuous_fst.comp continuous_subtype_val)

private noncomputable def boundaryFunction (n : ℕ) (i : Fin (n + 2))
    (B : TopCat.{v})
    (a : SSet.toTop.obj (SSet.horn.{v} (n + 1) i) ⟶ TopCat.pathObject B)
    (c : SSet.toTop.obj (Δ[n + 1] : SSet.{v}) ⟶ B ⨯ B)
    (z : PrismBoundary.{v} n i) : B := by
  classical
  exact if z.1.1 ∈ Set.range (hornInclusion.{v} (n + 1) i)
    then hornFormula n i B a z
    else if z.1.2 = 0 then zeroFormula n i B c z else oneFormula n i B c z

private theorem square_zero
    (n : ℕ) (i : Fin (n + 2)) (B : TopCat.{v})
    (a : SSet.toTop.obj (SSet.horn.{v} (n + 1) i) ⟶ TopCat.pathObject B)
    (c : SSet.toTop.obj (Δ[n + 1] : SSet.{v}) ⟶ B ⨯ B)
    (sq : CommSq a (SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι)
      (TopCat.pathEndpoints B) c)
    (x : realizedHorn.{v} (n + 1) i) :
    a x 0 = (c ≫ prod.fst) (hornInclusion.{v} (n + 1) i x) := by
  have hraw := ConcreteCategory.congr_hom sq.w x
  change TopCat.pathEndpoints B (a x) = c (hornInclusion (n + 1) i x) at hraw
  have h := congrArg (prod.fst : (B ⨯ B) ⟶ B) hraw
  simpa [TopCat.pathEndpoints, TopCat.pathEvalZero] using h

private theorem square_one
    (n : ℕ) (i : Fin (n + 2)) (B : TopCat.{v})
    (a : SSet.toTop.obj (SSet.horn.{v} (n + 1) i) ⟶ TopCat.pathObject B)
    (c : SSet.toTop.obj (Δ[n + 1] : SSet.{v}) ⟶ B ⨯ B)
    (sq : CommSq a (SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι)
      (TopCat.pathEndpoints B) c)
    (x : realizedHorn.{v} (n + 1) i) :
    a x 1 = (c ≫ prod.snd) (hornInclusion.{v} (n + 1) i x) := by
  have hraw := ConcreteCategory.congr_hom sq.w x
  change TopCat.pathEndpoints B (a x) = c (hornInclusion (n + 1) i x) at hraw
  have h := congrArg (prod.snd : (B ⨯ B) ⟶ B) hraw
  simpa [TopCat.pathEndpoints, TopCat.pathEvalOne] using h

private theorem boundaryFunction_eq_zero
    (n : ℕ) (i : Fin (n + 2)) (B : TopCat.{v})
    (a : SSet.toTop.obj (SSet.horn.{v} (n + 1) i) ⟶ TopCat.pathObject B)
    (c : SSet.toTop.obj (Δ[n + 1] : SSet.{v}) ⟶ B ⨯ B)
    (sq : CommSq a (SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι)
      (TopCat.pathEndpoints B) c)
    (z : PrismBoundary.{v} n i) (hz : z ∈ zeroSet n i) :
    boundaryFunction n i B a c z = zeroFormula n i B c z := by
  by_cases hh : z.1.1 ∈ Set.range (hornInclusion.{v} (n + 1) i)
  · simp only [boundaryFunction, hh, ↓reduceIte]
    obtain ⟨x, hx⟩ := hh
    have hxr : z.1.1 = hornInclusion.{v} (n + 1) i x := hx.symm
    unfold hornFormula zeroFormula
    rw [hxr]
    change a (SSet.realizedHornRetract (n + 1) i (by omega)
      (SSet.toTop.map (SSet.horn (n + 1) i).ι x))
        (TopCat.I.homeomorph.symm z.1.2) =
      (c ≫ prod.fst) (hornInclusion (n + 1) i x)
    rw [SSet.realizedHornRetract_ι]
    rw [show z.1.2 = 0 from hz]
    change a x 0 = _
    exact square_zero n i B a c sq x
  · have hz' : z.1.2 = 0 := hz
    simp [boundaryFunction, hh, hz']

private theorem boundaryFunction_eq_one
    (n : ℕ) (i : Fin (n + 2)) (B : TopCat.{v})
    (a : SSet.toTop.obj (SSet.horn.{v} (n + 1) i) ⟶ TopCat.pathObject B)
    (c : SSet.toTop.obj (Δ[n + 1] : SSet.{v}) ⟶ B ⨯ B)
    (sq : CommSq a (SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι)
      (TopCat.pathEndpoints B) c)
    (z : PrismBoundary.{v} n i) (hz : z ∈ oneSet n i) :
    boundaryFunction n i B a c z = oneFormula n i B c z := by
  by_cases hh : z.1.1 ∈ Set.range (hornInclusion.{v} (n + 1) i)
  · simp only [boundaryFunction, hh, ↓reduceIte]
    obtain ⟨x, hx⟩ := hh
    have hxr : z.1.1 = hornInclusion.{v} (n + 1) i x := hx.symm
    unfold hornFormula oneFormula
    rw [hxr]
    change a (SSet.realizedHornRetract (n + 1) i (by omega)
      (SSet.toTop.map (SSet.horn (n + 1) i).ι x))
        (TopCat.I.homeomorph.symm z.1.2) =
      (c ≫ prod.snd) (hornInclusion (n + 1) i x)
    rw [SSet.realizedHornRetract_ι]
    rw [show z.1.2 = 1 from hz]
    change a x 1 = _
    exact square_one n i B a c sq x
  · have hz' : z.1.2 = 1 := hz
    have hz0 : z.1.2 ≠ 0 := by
      rw [hz']
      norm_num
    simp [boundaryFunction, hh, hz0]

private theorem continuous_boundaryFunction
    (n : ℕ) (i : Fin (n + 2)) (B : TopCat.{v})
    (a : SSet.toTop.obj (SSet.horn.{v} (n + 1) i) ⟶ TopCat.pathObject B)
    (c : SSet.toTop.obj (Δ[n + 1] : SSet.{v}) ⟶ B ⨯ B)
    (sq : CommSq a (SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι)
      (TopCat.pathEndpoints B) c) :
    Continuous (boundaryFunction n i B a c) := by
  have hH : ContinuousOn (boundaryFunction n i B a c) (hornSet n i) := by
    apply (continuous_hornFormula n i B a).continuousOn.congr
    intro z hz
    have hz' : z.1.1 ∈ Set.range (hornInclusion.{v} (n + 1) i) := hz
    simp [boundaryFunction, hz']
  have hZ : ContinuousOn (boundaryFunction n i B a c) (zeroSet n i) := by
    apply (continuous_zeroFormula n i B c).continuousOn.congr
    intro z hz
    exact boundaryFunction_eq_zero n i B a c sq z hz
  have hO : ContinuousOn (boundaryFunction n i B a c) (oneSet n i) := by
    apply (continuous_oneFormula n i B c).continuousOn.congr
    intro z hz
    exact boundaryFunction_eq_one n i B a c sq z hz
  have hcover : hornSet.{v} n i ∪ zeroSet n i ∪ oneSet n i = Set.univ := by
    ext z
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    rcases z.2 with hz | hz | hz
    · exact Or.inl (Or.inl hz)
    · exact Or.inl (Or.inr hz)
    · exact Or.inr hz
  rw [← continuousOn_univ, ← hcover]
  exact (hH.union_of_isClosed hZ (hornSet_isClosed n i)
    (zeroSet_isClosed n i)).union_of_isClosed hO
      ((hornSet_isClosed n i).union (zeroSet_isClosed n i))
      (oneSet_isClosed n i)

private noncomputable def prismBoundaryMap
    (n : ℕ) (i : Fin (n + 2)) (B : TopCat.{v})
    (a : SSet.toTop.obj (SSet.horn.{v} (n + 1) i) ⟶ TopCat.pathObject B)
    (c : SSet.toTop.obj (Δ[n + 1] : SSet.{v}) ⟶ B ⨯ B)
    (sq : CommSq a (SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι)
      (TopCat.pathEndpoints B) c) : C(PrismBoundary.{v} n i, B) :=
  ⟨boundaryFunction n i B a c, continuous_boundaryFunction n i B a c sq⟩

private noncomputable def prismExtension
    (n : ℕ) (i : Fin (n + 2)) (B : TopCat.{v})
    (a : SSet.toTop.obj (SSet.horn.{v} (n + 1) i) ⟶ TopCat.pathObject B)
    (c : SSet.toTop.obj (Δ[n + 1] : SSet.{v}) ⟶ B ⨯ B)
    (sq : CommSq a (SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι)
      (TopCat.pathEndpoints B) c) :
    C(realizedSimplex.{v} (n + 1) × unitInterval, B) :=
  (prismBoundaryMap n i B a c sq).comp
    (TopCatRealizedHornIntervalPrismRetractionPreflight.realizedPrismRetract n i)

private theorem prismExtension_horn
    (n : ℕ) (i : Fin (n + 2)) (B : TopCat.{v})
    (a : SSet.toTop.obj (SSet.horn.{v} (n + 1) i) ⟶ TopCat.pathObject B)
    (c : SSet.toTop.obj (Δ[n + 1] : SSet.{v}) ⟶ B ⨯ B)
    (sq : CommSq a (SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι)
      (TopCat.pathEndpoints B) c)
    (x : realizedHorn.{v} (n + 1) i) (t : unitInterval) :
    prismExtension n i B a c sq (hornInclusion (n + 1) i x, t) =
      a x (TopCat.I.homeomorph.symm t) := by
  let z : PrismBoundary.{v} n i :=
    ⟨(hornInclusion (n + 1) i x, t), Or.inl ⟨x, rfl⟩⟩
  have hfix :=
    TopCatRealizedHornIntervalPrismRetractionPreflight.realizedPrismRetract_fix
      n i z
  change boundaryFunction n i B a c
    (TopCatRealizedHornIntervalPrismRetractionPreflight.realizedPrismRetract n i
      (hornInclusion (n + 1) i x, t)) = _
  rw [show
    TopCatRealizedHornIntervalPrismRetractionPreflight.realizedPrismRetract n i
      (hornInclusion (n + 1) i x, t) = z from hfix]
  simp only [boundaryFunction, z, Set.mem_range_self, ↓reduceIte]
  unfold hornFormula
  change a (SSet.realizedHornRetract (n + 1) i (by omega)
    (SSet.toTop.map (SSet.horn (n + 1) i).ι x))
      (TopCat.I.homeomorph.symm t) = _
  rw [SSet.realizedHornRetract_ι]

private theorem prismExtension_zero
    (n : ℕ) (i : Fin (n + 2)) (B : TopCat.{v})
    (a : SSet.toTop.obj (SSet.horn.{v} (n + 1) i) ⟶ TopCat.pathObject B)
    (c : SSet.toTop.obj (Δ[n + 1] : SSet.{v}) ⟶ B ⨯ B)
    (sq : CommSq a (SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι)
      (TopCat.pathEndpoints B) c)
    (x : realizedSimplex.{v} (n + 1)) :
    prismExtension n i B a c sq (x, 0) = (c ≫ prod.fst) x := by
  let z : PrismBoundary.{v} n i := ⟨(x, 0), Or.inr (Or.inl rfl)⟩
  have hfix :=
    TopCatRealizedHornIntervalPrismRetractionPreflight.realizedPrismRetract_fix
      n i z
  change boundaryFunction n i B a c
    (TopCatRealizedHornIntervalPrismRetractionPreflight.realizedPrismRetract n i
      (x, 0)) = _
  rw [show
    TopCatRealizedHornIntervalPrismRetractionPreflight.realizedPrismRetract n i
      (x, 0) = z from hfix]
  exact boundaryFunction_eq_zero n i B a c sq z rfl

private theorem prismExtension_one
    (n : ℕ) (i : Fin (n + 2)) (B : TopCat.{v})
    (a : SSet.toTop.obj (SSet.horn.{v} (n + 1) i) ⟶ TopCat.pathObject B)
    (c : SSet.toTop.obj (Δ[n + 1] : SSet.{v}) ⟶ B ⨯ B)
    (sq : CommSq a (SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι)
      (TopCat.pathEndpoints B) c)
    (x : realizedSimplex.{v} (n + 1)) :
    prismExtension n i B a c sq (x, 1) = (c ≫ prod.snd) x := by
  let z : PrismBoundary.{v} n i := ⟨(x, 1), Or.inr (Or.inr rfl)⟩
  have hfix :=
    TopCatRealizedHornIntervalPrismRetractionPreflight.realizedPrismRetract_fix
      n i z
  change boundaryFunction n i B a c
    (TopCatRealizedHornIntervalPrismRetractionPreflight.realizedPrismRetract n i
      (x, 1)) = _
  rw [show
    TopCatRealizedHornIntervalPrismRetractionPreflight.realizedPrismRetract n i
      (x, 1) = z from hfix]
  exact boundaryFunction_eq_one n i B a c sq z rfl

private def topCatTimePrism (n : ℕ) :
    C(realizedSimplex.{v} (n + 1) × TopCat.I.{v},
      realizedSimplex.{v} (n + 1) × unitInterval) where
  toFun z := (z.1, TopCat.I.homeomorph z.2)
  continuous_toFun := continuous_fst.prodMk
    (TopCat.I.homeomorph.continuous.comp continuous_snd)

private noncomputable def pathLift
    (n : ℕ) (i : Fin (n + 2)) (B : TopCat.{v})
    (a : SSet.toTop.obj (SSet.horn.{v} (n + 1) i) ⟶ TopCat.pathObject B)
    (c : SSet.toTop.obj (Δ[n + 1] : SSet.{v}) ⟶ B ⨯ B)
    (sq : CommSq a (SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι)
      (TopCat.pathEndpoints B) c) :
    SSet.toTop.obj (Δ[n + 1] : SSet.{v}) ⟶ TopCat.pathObject B :=
  TopCat.ofHom ((prismExtension n i B a c sq).comp (topCatTimePrism n) |>.curry)

private theorem pathLift_horn
    (n : ℕ) (i : Fin (n + 2)) (B : TopCat.{v})
    (a : SSet.toTop.obj (SSet.horn.{v} (n + 1) i) ⟶ TopCat.pathObject B)
    (c : SSet.toTop.obj (Δ[n + 1] : SSet.{v}) ⟶ B ⨯ B)
    (sq : CommSq a (SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι)
      (TopCat.pathEndpoints B) c) :
    SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι ≫ pathLift n i B a c sq = a := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro t
  change prismExtension n i B a c sq
      (hornInclusion (n + 1) i x, TopCat.I.homeomorph t) = a x t
  rw [prismExtension_horn]
  simp

private theorem pathLift_endpoints
    (n : ℕ) (i : Fin (n + 2)) (B : TopCat.{v})
    (a : SSet.toTop.obj (SSet.horn.{v} (n + 1) i) ⟶ TopCat.pathObject B)
    (c : SSet.toTop.obj (Δ[n + 1] : SSet.{v}) ⟶ B ⨯ B)
    (sq : CommSq a (SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι)
      (TopCat.pathEndpoints B) c) :
    pathLift n i B a c sq ≫ TopCat.pathEndpoints B = c := by
  apply prod.hom_ext
  · simp only [Category.assoc, TopCat.pathEndpoints, prod.lift_fst]
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change prismExtension n i B a c sq (x, TopCat.I.homeomorph (0 : TopCat.I.{v})) =
      (c ≫ prod.fst) x
    simpa using prismExtension_zero n i B a c sq x
  · simp only [Category.assoc, TopCat.pathEndpoints, prod.lift_snd]
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change prismExtension n i B a c sq (x, TopCat.I.homeomorph (1 : TopCat.I.{v})) =
      (c ≫ prod.snd) x
    simpa using prismExtension_one n i B a c sq x

private theorem realizedHorn_pathEndpoints_hasLift
    (n : ℕ) (i : Fin (n + 2)) (B : TopCat.{v})
    {a : SSet.toTop.obj (SSet.horn.{v} (n + 1) i) ⟶ TopCat.pathObject B}
    {c : SSet.toTop.obj (Δ[n + 1] : SSet.{v}) ⟶ B ⨯ B}
    (sq : CommSq a (SSet.toTop.map (SSet.horn.{v} (n + 1) i).ι)
      (TopCat.pathEndpoints B) c) : sq.HasLift :=
  CommSq.HasLift.mk' ⟨pathLift n i B a c sq,
    pathLift_horn n i B a c sq, pathLift_endpoints n i B a c sq⟩

private theorem pathEndpoints_mem_realizedHornRLP (B : TopCat.{v}) :
    TopCat.realizedHornInclusions.{v}.rlp (TopCat.pathEndpoints B) := by
  intro A D g hg
  simp only [TopCat.realizedHornInclusions, MorphismProperty.iSup_iff] at hg
  obtain ⟨n, ⟨i⟩⟩ := hg
  exact ⟨fun sq => realizedHorn_pathEndpoints_hasLift n i B sq⟩

end TopCatPathEndpointsSelectedFibrationResume

namespace TopCat.modelCategory

open HomotopicalAlgebra

universe w

private theorem pathEndpoints_fibration_data (B : TopCat.{w}) :
    let _ : ModelCategory TopCat.{w} := TopCat.modelCategory
    Fibration (TopCat.pathEndpoints B) := by
  let _ : ModelCategory TopCat.{w} := TopCat.modelCategory
  exact ⟨TopCatPathEndpointsSelectedFibrationResume.pathEndpoints_mem_realizedHornRLP B⟩

/-- Endpoint evaluation of compact-open paths is a fibration in the selected
TopCat model structure. -/
theorem pathEndpoints_fibration (B : TopCat.{w}) :
    let _ : ModelCategory TopCat.{w} := TopCat.modelCategory
    Fibration (TopCat.pathEndpoints B) :=
  pathEndpoints_fibration_data B

end TopCat.modelCategory

/-!
# Homotopy-square transport for compact-open homotopy fibers

A homotopy from q after s to p induces a continuous map from the compact-open
homotopy fiber of p to that of q by prepending the homotopy path. The map
retains the total coordinate through s, has a literal full-path formula, and
is a weak homotopy equivalence whenever s is.

The endpoint-fibration, affine-prism, mapping-path, right-properness,
strict-fiber, and reparametrization scaffolding is implementation-private.
Identity, strict-square, and composition coherence homotopies are public.
No global model-category, fibration, or properness instance is installed.
-/

open CategoryTheory CategoryTheory.Limits Topology HomotopicalAlgebra
open scoped unitInterval SSet.modelCategoryQuillen

universe u

namespace TopCatHomotopySquarePreflight

noncomputable section

private def fiberRootPath
    {X B : TopCat.{u}} (f : X ⟶ B) (b : B)
    (z : TopCat.homotopyFiber f b) :
    Path (f (TopCat.homotopyFiberToTotal f b z)) b where
  toFun t := TopCat.homotopyFiberPath f b z (TopCat.I.homeomorph.symm t)
  continuous_toFun :=
    (TopCat.homotopyFiberPath f b z).continuous.comp
      TopCat.I.homeomorph.symm.continuous
  source' := by
    have h := ConcreteCategory.congr_hom
      (TopCat.homotopyPullbackPath_evalZero f
        (TopCat.const (X := TopCat.of PUnit) b)) z
    exact h
  target' := by
    have hOne : TopCat.I.homeomorph.symm (1 : unitInterval) =
        (1 : TopCat.I.{u}) := by
      apply TopCat.I.homeomorph.injective
      simp
    have h := ConcreteCategory.congr_hom
      (TopCat.homotopyPullbackPath_evalOne f
        (TopCat.const (X := TopCat.of PUnit) b)) z
    change TopCat.homotopyFiberPath f b z
      (TopCat.I.homeomorph.symm 1) = b
    rw [hOne]
    exact h

private theorem fiberRootPath_continuous_family
    {X B : TopCat.{u}} (f : X ⟶ B) (b : B) :
    Continuous (fun z : TopCat.homotopyFiber f b × unitInterval =>
      fiberRootPath f b z.1 z.2) := by
  exact continuous_eval.comp
    (((TopCat.homotopyFiberPath f b).hom.continuous.comp continuous_fst).prodMk
      (TopCat.I.homeomorph.symm.continuous.comp continuous_snd))

/-- The pointwise path supplied by a homotopy, with its literal orientation. -/
private def homotopyPointPath
    {X B : TopCat.{u}} {a₀ a₁ : X ⟶ B}
    (H : ContinuousMap.Homotopy a₀.hom a₁.hom) (x : X) :
    Path (a₀ x) (a₁ x) where
  toFun t := H (t, x)
  continuous_toFun := H.continuous.comp
    (continuous_id.prodMk continuous_const)
  source' := H.map_zero_left x
  target' := H.map_one_left x

private theorem homotopyPointPath_continuous_family
    {X B : TopCat.{u}} {a₀ a₁ : X ⟶ B}
    (H : ContinuousMap.Homotopy a₀.hom a₁.hom) :
    Continuous (fun z : X × unitInterval => homotopyPointPath H z.1 z.2) := by
  exact H.continuous.comp (continuous_snd.prodMk continuous_fst)

/-- The homotopy path followed by the fiber path varies continuously on the standard interval. -/
private theorem prependHomotopyFiberPath_continuous_family
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    Continuous (fun z : TopCat.homotopyFiber p b × unitInterval =>
      ((homotopyPointPath H
        (TopCat.homotopyFiberToTotal p b z.1)).trans
          (fiberRootPath p b z.1)) z.2) := by
  have hH : Continuous (fun z : TopCat.homotopyFiber p b × unitInterval =>
      homotopyPointPath H (TopCat.homotopyFiberToTotal p b z.1) z.2) :=
    (homotopyPointPath_continuous_family H).comp
      (((TopCat.homotopyFiberToTotal p b).hom.continuous.comp
        continuous_fst).prodMk continuous_snd)
  exact Path.trans_continuous_family
    (fun z : TopCat.homotopyFiber p b =>
      homotopyPointPath H (TopCat.homotopyFiberToTotal p b z)) hH
    (fun z : TopCat.homotopyFiber p b => fiberRootPath p b z)
    (fiberRootPath_continuous_family p b)

/-- Reparametrize the same concatenated family by the native interval homeomorphism. -/
private theorem prependHomotopyFiberPath_continuous
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    Continuous (fun z : TopCat.homotopyFiber p b × TopCat.I.{u} =>
      ((homotopyPointPath H
        (TopCat.homotopyFiberToTotal p b z.1)).trans
          (fiberRootPath p b z.1)) (TopCat.I.homeomorph z.2)) := by
  have hinterval : Continuous (fun z :
      TopCat.homotopyFiber p b × TopCat.I.{u} =>
      (z.1, TopCat.I.homeomorph z.2)) :=
    continuous_fst.prodMk
      (TopCat.I.homeomorph.continuous.comp continuous_snd)
  have hcomp := (prependHomotopyFiberPath_continuous_family s p q b H).comp hinterval
  refine hcomp.congr ?_
  intro z
  rfl

private def prependHomotopyFiberPath
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    TopCat.homotopyFiber p b ⟶ TopCat.pathObject B :=
  TopCat.ofHom <| ContinuousMap.curry
    { toFun := fun z =>
        ((homotopyPointPath H
          (TopCat.homotopyFiberToTotal p b z.1)).trans
            (fiberRootPath p b z.1)) (TopCat.I.homeomorph z.2)
      continuous_toFun := prependHomotopyFiberPath_continuous s p q b H }

@[reassoc]
private theorem prependHomotopyFiberPath_evalZero
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    prependHomotopyFiberPath s p q b H ≫ TopCat.pathEvalZero B =
      (TopCat.homotopyFiberToTotal p b ≫ s) ≫ q := by
  apply TopCat.ext
  intro z
  change ((homotopyPointPath H
      (TopCat.homotopyFiberToTotal p b z)).trans
        (fiberRootPath p b z))
      (TopCat.I.homeomorph (0 : TopCat.I.{u})) = _
  rw [TopCat.I.homeomorph_zero]
  exact ((homotopyPointPath H
    (TopCat.homotopyFiberToTotal p b z)).trans
      (fiberRootPath p b z)).source'

@[reassoc]
private theorem prependHomotopyFiberPath_evalOne
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    prependHomotopyFiberPath s p q b H ≫ TopCat.pathEvalOne B =
      TopCat.const (X := TopCat.homotopyFiber p b) b := by
  apply TopCat.ext
  intro z
  change ((homotopyPointPath H
      (TopCat.homotopyFiberToTotal p b z)).trans
        (fiberRootPath p b z))
      (TopCat.I.homeomorph (1 : TopCat.I.{u})) = b
  rw [TopCat.I.homeomorph_one]
  exact ((homotopyPointPath H
    (TopCat.homotopyFiberToTotal p b z)).trans
      (fiberRootPath p b z)).target'

/-- The map of compact-open homotopy fibers induced by the homotopy square. -/
private def homotopyFiberMapOfHomotopy
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    TopCat.homotopyFiber p b ⟶ TopCat.homotopyFiber q b :=
  pullback.lift
    (Limits.prod.lift (TopCat.homotopyFiberToTotal p b ≫ s)
      (TopCat.homotopyPullbackRight p
        (TopCat.const (X := TopCat.of PUnit) b)))
    (prependHomotopyFiberPath s p q b H)
    (by
      apply Limits.prod.hom_ext
      · simpa [TopCat.pathEndpoints, Category.assoc] using
          (prependHomotopyFiberPath_evalZero s p q b H).symm
      · calc
          (Limits.prod.lift (TopCat.homotopyFiberToTotal p b ≫ s)
                (TopCat.homotopyPullbackRight p (TopCat.const b)) ≫
              Limits.prod.map q (TopCat.const b)) ≫ Limits.prod.snd =
              TopCat.const b := by
                rw [Category.assoc, Limits.prod.map_snd]
                rw [← Category.assoc, Limits.prod.lift_snd]
                apply TopCat.ext
                intro z
                exact congrArg (fun _ : PUnit => b)
                  (Subsingleton.elim
                    (TopCat.homotopyPullbackRight p
                      (TopCat.const (X := TopCat.of PUnit) b) z)
                    PUnit.unit)
          _ = (prependHomotopyFiberPath s p q b H ≫
              TopCat.pathEndpoints B) ≫ Limits.prod.snd := by
                simpa [TopCat.pathEndpoints] using
                  (prependHomotopyFiberPath_evalOne s p q b H).symm)

@[reassoc (attr := simp)]
private theorem homotopyFiberMapOfHomotopy_toTotal
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    homotopyFiberMapOfHomotopy s p q b H ≫
        TopCat.homotopyFiberToTotal q b =
      TopCat.homotopyFiberToTotal p b ≫ s := by
  change homotopyFiberMapOfHomotopy s p q b H ≫
      TopCat.homotopyPullbackLeft q (TopCat.const b) = _
  rw [homotopyFiberMapOfHomotopy, TopCat.homotopyPullbackLeft,
    ← Category.assoc, pullback.lift_fst]
  simp

@[reassoc]
private theorem homotopyFiberMapOfHomotopy_path_map
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    homotopyFiberMapOfHomotopy s p q b H ≫
        TopCat.homotopyFiberPath q b =
      prependHomotopyFiberPath s p q b H := by
  change homotopyFiberMapOfHomotopy s p q b H ≫
      TopCat.homotopyPullbackPath q (TopCat.const b) = _
  rw [homotopyFiberMapOfHomotopy, TopCat.homotopyPullbackPath,
    pullback.lift_snd]

/-- Exact complete-path formula. -/
@[simp]
private theorem homotopyFiberMapOfHomotopy_path
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom)
    (z : TopCat.homotopyFiber p b) (t : TopCat.I.{u}) :
    TopCat.homotopyFiberPath q b
        (homotopyFiberMapOfHomotopy s p q b H z) t =
      ((homotopyPointPath H (TopCat.homotopyFiberToTotal p b z)).trans
        (fiberRootPath p b z)) (TopCat.I.homeomorph t) := by
  change (homotopyFiberMapOfHomotopy s p q b H ≫
      TopCat.homotopyPullbackPath q (TopCat.const b)) z t = _
  rw [homotopyFiberMapOfHomotopy_path_map]
  rfl

/-! Private scaffolding for public canonical whole-map coherence. -/

private def identitySquareHomotopy {X B : TopCat.{u}} (p : X ⟶ B) :
    ContinuousMap.Homotopy ((𝟙 X) ≫ p).hom p.hom :=
  (ContinuousMap.Homotopy.refl p.hom).cast (by simp) rfl

private def strictSquareHomotopy
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (h : s ≫ q = p) :
    ContinuousMap.Homotopy (s ≫ q).hom p.hom :=
  (ContinuousMap.Homotopy.refl p.hom).cast
    (by rw [h]) rfl

private def precomposeSquareHomotopy
    {X Y Z B : TopCat.{u}} (s : X ⟶ Y) (t : Y ⟶ Z)
    (q : Y ⟶ B) (r : Z ⟶ B)
    (K : ContinuousMap.Homotopy (t ≫ r).hom q.hom) :
    ContinuousMap.Homotopy ((s ≫ t) ≫ r).hom (s ≫ q).hom :=
  (K.comp (ContinuousMap.Homotopy.refl s.hom)).cast
    (by rfl) (by rfl)

private def compositeSquareHomotopy
    {X Y Z B : TopCat.{u}}
    (s : X ⟶ Y) (t : Y ⟶ Z) (p : X ⟶ B) (q : Y ⟶ B) (r : Z ⟶ B)
    (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom)
    (K : ContinuousMap.Homotopy (t ≫ r).hom q.hom) :
    ContinuousMap.Homotopy ((s ≫ t) ≫ r).hom p.hom :=
  (precomposeSquareHomotopy s t q r K).trans H

private def blendReparam (r : unitInterval → unitInterval)
    (s t : unitInterval) : unitInterval :=
  ⟨(unitInterval.symm s : ℝ) • (r t : ℝ) + (s : ℝ) • (t : ℝ),
    convex_Icc _ _ (r t).2 t.2 (by unit_interval) (by unit_interval)
      (by simp) ⟩

private theorem blendReparam_continuous (r : unitInterval → unitInterval)
    (hr : Continuous r) :
    Continuous (fun st : unitInterval × unitInterval =>
      blendReparam r st.1 st.2) := by
  apply Continuous.subtype_mk
  fun_prop

private theorem blendReparam_zero (r : unitInterval → unitInterval)
    (t : unitInterval) : blendReparam r 0 t = r t := by
  apply Subtype.ext
  simp [blendReparam]

private theorem blendReparam_one (r : unitInterval → unitInterval)
    (t : unitInterval) : blendReparam r 1 t = t := by
  apply Subtype.ext
  simp [blendReparam]

private theorem blendReparam_left (r : unitInterval → unitInterval)
    (hr0 : r 0 = 0) (s : unitInterval) :
    blendReparam r s 0 = 0 := by
  apply Subtype.ext
  simp [blendReparam, hr0]

private theorem blendReparam_right (r : unitInterval → unitInterval)
    (hr1 : r 1 = 1) (s : unitInterval) :
    blendReparam r s 1 = 1 := by
  apply Subtype.ext
  simp [blendReparam, hr1]

private def intervalZero (A : TopCat.{u}) :
    A ⟶ TopCat.of (unitInterval × (A : Type u)) :=
  TopCat.ofHom
    { toFun := fun a => (0, a)
      continuous_toFun := continuous_const.prodMk continuous_id }

private def intervalOne (A : TopCat.{u}) :
    A ⟶ TopCat.of (unitInterval × (A : Type u)) :=
  TopCat.ofHom
    { toFun := fun a => (1, a)
      continuous_toFun := continuous_const.prodMk continuous_id }

private def intervalSnd (A : TopCat.{u}) :
    TopCat.of (unitInterval × (A : Type u)) ⟶ A :=
  TopCat.ofHom ContinuousMap.snd

@[simp]
private theorem intervalZero_snd (A : TopCat.{u}) :
    intervalZero A ≫ intervalSnd A = 𝟙 A := by
  rfl

@[simp]
private theorem intervalOne_snd (A : TopCat.{u}) :
    intervalOne A ≫ intervalSnd A = 𝟙 A := by
  rfl

/-- Reparametrize a whole compact-open path family, blending from `r` to the
identity as the outer parameter runs from zero to one. -/
private def reparamPathFamily {A B : TopCat.{u}}
    (p : A ⟶ TopCat.pathObject B) (r : unitInterval → unitInterval)
    (hr : Continuous r) :
    TopCat.of (unitInterval × (A : Type u)) ⟶ TopCat.pathObject B :=
  TopCat.ofHom <| ContinuousMap.curry
    { toFun := fun z =>
        p z.1.2
          (TopCat.I.homeomorph.symm
            (blendReparam r z.1.1 (TopCat.I.homeomorph z.2)))
      continuous_toFun := by
        have hp : Continuous (fun z :
            (unitInterval × (A : Type u)) × (TopCat.I.{u} : Type u) =>
            p z.1.2) :=
          p.hom.continuous.comp (continuous_snd.comp continuous_fst)
        have htI : Continuous (fun z :
            (unitInterval × (A : Type u)) × (TopCat.I.{u} : Type u) =>
            TopCat.I.homeomorph z.2) :=
          TopCat.I.homeomorph.continuous.comp continuous_snd
        have hs : Continuous (fun z :
            (unitInterval × (A : Type u)) × (TopCat.I.{u} : Type u) =>
            z.1.1) := continuous_fst.comp continuous_fst
        have hblend : Continuous (fun z :
            (unitInterval × (A : Type u)) × (TopCat.I.{u} : Type u) =>
            blendReparam r z.1.1 (TopCat.I.homeomorph z.2)) :=
          (blendReparam_continuous r hr).comp (hs.prodMk htI)
        exact continuous_eval.comp
          (hp.prodMk (TopCat.I.homeomorph.symm.continuous.comp hblend)) }

private theorem reparamPathFamily_evalZero {A B : TopCat.{u}}
    (p : A ⟶ TopCat.pathObject B) (r : unitInterval → unitInterval)
    (hr : Continuous r) (hr0 : r 0 = 0) :
    reparamPathFamily p r hr ≫ TopCat.pathEvalZero B =
      intervalSnd A ≫ p ≫ TopCat.pathEvalZero B := by
  apply TopCat.ext
  rintro ⟨s, a⟩
  have hTopZero : TopCat.I.homeomorph.symm (0 : unitInterval) =
      (0 : TopCat.I.{u}) := by
    apply TopCat.I.homeomorph.injective
    simp
  change p a (TopCat.I.homeomorph.symm
      (blendReparam r s (TopCat.I.homeomorph (0 : TopCat.I.{u})))) = p a 0
  rw [TopCat.I.homeomorph_zero, blendReparam_left r hr0, hTopZero]

private theorem reparamPathFamily_evalOne {A B : TopCat.{u}}
    (p : A ⟶ TopCat.pathObject B) (r : unitInterval → unitInterval)
    (hr : Continuous r) (hr1 : r 1 = 1) :
    reparamPathFamily p r hr ≫ TopCat.pathEvalOne B =
      intervalSnd A ≫ p ≫ TopCat.pathEvalOne B := by
  apply TopCat.ext
  rintro ⟨s, a⟩
  have hTopOne : TopCat.I.homeomorph.symm (1 : unitInterval) =
      (1 : TopCat.I.{u}) := by
    apply TopCat.I.homeomorph.injective
    simp
  change p a (TopCat.I.homeomorph.symm
      (blendReparam r s (TopCat.I.homeomorph (1 : TopCat.I.{u})))) = p a 1
  rw [TopCat.I.homeomorph_one, blendReparam_right r hr1, hTopOne]

private theorem intervalOne_comp_reparamPathFamily {A B : TopCat.{u}}
    (p : A ⟶ TopCat.pathObject B) (r : unitInterval → unitInterval)
    (hr : Continuous r) :
    intervalOne A ≫ reparamPathFamily p r hr = p := by
  apply TopCat.ext
  intro a
  apply ContinuousMap.ext
  intro t
  change p a (TopCat.I.homeomorph.symm
      (blendReparam r 1 (TopCat.I.homeomorph t))) = p a t
  rw [blendReparam_one, TopCat.I.homeomorph.symm_apply_apply]

/-! ## Reparametrization inside a homotopy fiber -/

private def homotopyFiberReparamLift
    {A X B : TopCat.{u}} (f : X ⟶ B) (b : B)
    (target : A ⟶ TopCat.homotopyFiber f b)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1) :
    TopCat.of (unitInterval × (A : Type u)) ⟶ TopCat.homotopyFiber f b :=
  pullback.lift
    (Limits.prod.lift
      (intervalSnd A ≫ target ≫ TopCat.homotopyFiberToTotal f b)
      (intervalSnd A ≫ target ≫
        TopCat.homotopyPullbackRight f (TopCat.const b)))
    (reparamPathFamily (target ≫ TopCat.homotopyFiberPath f b) r hr)
    (by
      apply Limits.prod.hom_ext
      · calc
          (Limits.prod.lift
                (intervalSnd A ≫ target ≫ TopCat.homotopyFiberToTotal f b)
                (intervalSnd A ≫ target ≫
                  TopCat.homotopyPullbackRight f (TopCat.const b)) ≫
              Limits.prod.map f (TopCat.const b)) ≫ Limits.prod.fst =
              intervalSnd A ≫ target ≫
                TopCat.homotopyFiberToTotal f b ≫ f := by
                  simp [Category.assoc]
          _ = reparamPathFamily
                (target ≫ TopCat.homotopyFiberPath f b) r hr ≫
              TopCat.pathEvalZero B := by
                rw [reparamPathFamily_evalZero _ _ _ hr0]
                have h := congrArg
                  (fun k => intervalSnd A ≫ target ≫ k)
                  (TopCat.homotopyPullbackPath_evalZero f
                    (TopCat.const (X := TopCat.of PUnit) b))
                simpa [Category.assoc] using h.symm
          _ = (reparamPathFamily
                (target ≫ TopCat.homotopyFiberPath f b) r hr ≫
              TopCat.pathEndpoints B) ≫ Limits.prod.fst := by
                simp [TopCat.pathEndpoints]
      · calc
          (Limits.prod.lift
                (intervalSnd A ≫ target ≫ TopCat.homotopyFiberToTotal f b)
                (intervalSnd A ≫ target ≫
                  TopCat.homotopyPullbackRight f (TopCat.const b)) ≫
              Limits.prod.map f (TopCat.const b)) ≫ Limits.prod.snd =
              intervalSnd A ≫ target ≫
                TopCat.homotopyPullbackRight f (TopCat.const b) ≫
                  TopCat.const b := by
                    simp [Category.assoc]
          _ = reparamPathFamily
                (target ≫ TopCat.homotopyFiberPath f b) r hr ≫
              TopCat.pathEvalOne B := by
                rw [reparamPathFamily_evalOne _ _ _ hr1]
                have h := congrArg
                  (fun k => intervalSnd A ≫ target ≫ k)
                  (TopCat.homotopyPullbackPath_evalOne f
                    (TopCat.const (X := TopCat.of PUnit) b))
                simpa [Category.assoc] using h.symm
          _ = (reparamPathFamily
                (target ≫ TopCat.homotopyFiberPath f b) r hr ≫
              TopCat.pathEndpoints B) ≫ Limits.prod.snd := by
                simp [TopCat.pathEndpoints])

private theorem homotopyFiberReparamLift_toTotal
    {A X B : TopCat.{u}} (f : X ⟶ B) (b : B)
    (target : A ⟶ TopCat.homotopyFiber f b)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1) :
    homotopyFiberReparamLift f b target r hr hr0 hr1 ≫
        TopCat.homotopyFiberToTotal f b =
      intervalSnd A ≫ target ≫ TopCat.homotopyFiberToTotal f b := by
  change homotopyFiberReparamLift f b target r hr hr0 hr1 ≫
      TopCat.homotopyPullbackLeft f (TopCat.const b) = _
  rw [homotopyFiberReparamLift,
    ← Category.assoc, pullback.lift_fst]
  simp

private theorem homotopyFiberReparamLift_path
    {A X B : TopCat.{u}} (f : X ⟶ B) (b : B)
    (target : A ⟶ TopCat.homotopyFiber f b)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1) :
    homotopyFiberReparamLift f b target r hr hr0 hr1 ≫
        TopCat.homotopyFiberPath f b =
      reparamPathFamily (target ≫ TopCat.homotopyFiberPath f b) r hr := by
  change homotopyFiberReparamLift f b target r hr hr0 hr1 ≫
      TopCat.homotopyPullbackPath f (TopCat.const b) = _
  rw [homotopyFiberReparamLift, TopCat.homotopyPullbackPath,
    pullback.lift_snd]

private theorem intervalOne_comp_homotopyFiberReparamLift
    {A X B : TopCat.{u}} (f : X ⟶ B) (b : B)
    (target : A ⟶ TopCat.homotopyFiber f b)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1) :
    intervalOne A ≫ homotopyFiberReparamLift f b target r hr hr0 hr1 =
      target := by
  apply TopCat.homotopyPullback_hom_ext
  · rw [Category.assoc, homotopyFiberReparamLift_toTotal]
    rw [← Category.assoc, intervalOne_snd, Category.id_comp]
  · apply TopCat.isTerminalPUnit.hom_ext
  · rw [Category.assoc, homotopyFiberReparamLift_path,
      intervalOne_comp_reparamPathFamily]

private def homotopyFiberReparamHomotopy
    {A X B : TopCat.{u}} (f : X ⟶ B) (b : B)
    (source target : A ⟶ TopCat.homotopyFiber f b)
    (r : unitInterval → unitInterval) (hr : Continuous r)
    (hr0 : r 0 = 0) (hr1 : r 1 = 1)
    (htotal : source ≫ TopCat.homotopyFiberToTotal f b =
      target ≫ TopCat.homotopyFiberToTotal f b)
    (hpath : source ≫ TopCat.homotopyFiberPath f b =
      intervalZero A ≫
        reparamPathFamily (target ≫ TopCat.homotopyFiberPath f b) r hr) :
    ContinuousMap.Homotopy source.hom target.hom := by
  let lift := homotopyFiberReparamLift f b target r hr hr0 hr1
  have hzero : intervalZero A ≫ lift = source := by
    apply TopCat.homotopyPullback_hom_ext
    · rw [Category.assoc, homotopyFiberReparamLift_toTotal]
      rw [← Category.assoc, intervalZero_snd, Category.id_comp]
      exact htotal.symm
    · apply TopCat.isTerminalPUnit.hom_ext
    · rw [Category.assoc, homotopyFiberReparamLift_path]
      exact hpath.symm
  have hone : intervalOne A ≫ lift = target :=
    intervalOne_comp_homotopyFiberReparamLift f b target r hr hr0 hr1
  exact
    { toContinuousMap := lift.hom
      map_zero_left := fun a => by
        simpa [intervalZero] using ConcreteCategory.congr_hom hzero a
      map_one_left := fun a => by
        simpa [intervalOne] using ConcreteCategory.congr_hom hone a }

/-! ## Homotopy-coherent identity and composition -/

private def reflTransReparam (t : unitInterval) : unitInterval :=
  ⟨max 0 (2 * t - 1),
    ⟨le_max_left _ _, max_le (by norm_num) (by
      have ht := t.2.2
      linarith)⟩⟩

private theorem reflTransReparam_continuous :
    Continuous reflTransReparam := by
  apply Continuous.subtype_mk
  exact continuous_const.max
    ((continuous_const.mul continuous_subtype_val).sub continuous_const)

private theorem reflTransReparam_zero : reflTransReparam 0 = 0 := by
  apply Subtype.ext
  norm_num [reflTransReparam]

private theorem reflTransReparam_one : reflTransReparam 1 = 1 := by
  apply Subtype.ext
  norm_num [reflTransReparam]

private theorem refl_trans_eq_reparam {B : TopCat.{u}} {x y : B}
    (p : Path x y) :
    (Path.refl x).trans p =
      p.reparam reflTransReparam reflTransReparam_continuous
        reflTransReparam_zero reflTransReparam_one := by
  apply Path.ext
  funext t
  simp only [Path.trans_apply, Path.coe_reparam]
  split_ifs with ht
  · have hlin : 2 * (t : ℝ) - 1 ≤ 0 := by linarith
    simp [Path.refl, reflTransReparam, max_eq_left hlin]
    rfl
  · have hlin : 0 ≤ 2 * (t : ℝ) - 1 := by
      have ht' : 1 / 2 ≤ (t : ℝ) := (not_le.1 ht).le
      linarith
    simp [reflTransReparam, max_eq_right hlin]

private def assocReparam : unitInterval → unitInterval := fun t =>
  ⟨Path.Homotopy.transAssocReparamAux t,
    Path.Homotopy.transAssocReparamAux_mem_I t⟩

private theorem assocReparam_continuous : Continuous assocReparam := by
  apply Continuous.subtype_mk
  exact Path.Homotopy.continuous_transAssocReparamAux

private theorem assocReparam_zero : assocReparam 0 = 0 := by
  apply Subtype.ext
  exact Path.Homotopy.transAssocReparamAux_zero

private theorem assocReparam_one : assocReparam 1 = 1 := by
  apply Subtype.ext
  exact Path.Homotopy.transAssocReparamAux_one

private theorem trans_assoc_eq_reparam {B : TopCat.{u}}
    {x₀ x₁ x₂ x₃ : B} (p : Path x₀ x₁)
    (q : Path x₁ x₂) (r : Path x₂ x₃) :
    (p.trans q).trans r =
      (p.trans (q.trans r)).reparam assocReparam assocReparam_continuous
        assocReparam_zero assocReparam_one := by
  calc
    (p.trans q).trans r =
        (p.trans (q.trans r)).reparam
          (fun t => ⟨Path.Homotopy.transAssocReparamAux t,
            Path.Homotopy.transAssocReparamAux_mem_I t⟩)
          (by fun_prop)
          (Subtype.ext Path.Homotopy.transAssocReparamAux_zero)
          (Subtype.ext Path.Homotopy.transAssocReparamAux_one) :=
      Path.Homotopy.trans_assoc_reparam p q r
    _ = (p.trans (q.trans r)).reparam assocReparam
          assocReparam_continuous assocReparam_zero assocReparam_one := by
      apply Path.ext
      rfl

private def IdentityCoherenceStatement : Prop :=
  ∀ {X B : TopCat.{u}} (p : X ⟶ B) (b : B),
    Nonempty <| ContinuousMap.Homotopy
      (homotopyFiberMapOfHomotopy (𝟙 X) p p b
        (identitySquareHomotopy p)).hom
      ((𝟙 (TopCat.homotopyFiber p b) :
        TopCat.homotopyFiber p b ⟶ TopCat.homotopyFiber p b).hom)

private def ConstantSquareCoherenceStatement : Prop :=
  ∀ {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (h : s ≫ q = p),
    Nonempty <| ContinuousMap.Homotopy
      (homotopyFiberMapOfHomotopy s p q b
        (strictSquareHomotopy s p q h)).hom
      (TopCat.homotopyPullbackMap s (𝟙 (TopCat.of PUnit)) (𝟙 B)
        (by simp [h]) (by simp)).hom

private def CompositionCoherenceStatement : Prop :=
  ∀ {X Y Z B : TopCat.{u}}
    (s : X ⟶ Y) (t : Y ⟶ Z) (p : X ⟶ B) (q : Y ⟶ B) (r : Z ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom)
    (K : ContinuousMap.Homotopy (t ≫ r).hom q.hom),
    Nonempty <| ContinuousMap.Homotopy
      (homotopyFiberMapOfHomotopy s p q b H ≫
        homotopyFiberMapOfHomotopy t q r b K).hom
      (homotopyFiberMapOfHomotopy (s ≫ t) p r b
        (compositeSquareHomotopy s t p q r H K)).hom

private theorem identitySquareHomotopy_pointPath
    {X B : TopCat.{u}} (p : X ⟶ B) (x : X) :
    homotopyPointPath (identitySquareHomotopy p) x = Path.refl (p x) := by
  apply Path.ext
  funext t
  rfl

private theorem identityCoherenceStatement_proof :
    IdentityCoherenceStatement.{u} := by
  intro X B p b
  refine ⟨?_⟩
  apply homotopyFiberReparamHomotopy p b
    (homotopyFiberMapOfHomotopy (𝟙 X) p p b
      (identitySquareHomotopy p))
    (𝟙 (TopCat.homotopyFiber p b)) reflTransReparam
    reflTransReparam_continuous reflTransReparam_zero
    reflTransReparam_one
  · exact homotopyFiberMapOfHomotopy_toTotal
      (𝟙 X) p p b (identitySquareHomotopy p)
  · rw [homotopyFiberMapOfHomotopy_path_map]
    apply TopCat.ext
    intro z
    apply ContinuousMap.ext
    intro t
    have h := congrArg
      (fun path : Path
          (p (TopCat.homotopyFiberToTotal p b z)) b =>
        path (TopCat.I.homeomorph t))
      (refl_trans_eq_reparam (fiberRootPath p b z))
    change ((homotopyPointPath (identitySquareHomotopy p)
          (TopCat.homotopyFiberToTotal p b z)).trans
        (fiberRootPath p b z)) (TopCat.I.homeomorph t) =
      TopCat.homotopyFiberPath p b z
        (TopCat.I.homeomorph.symm
          (blendReparam reflTransReparam 0 (TopCat.I.homeomorph t)))
    rw [blendReparam_zero, identitySquareHomotopy_pointPath]
    change ((Path.refl (p (TopCat.homotopyFiberToTotal p b z))).trans
        (fiberRootPath p b z)) (TopCat.I.homeomorph t) =
      fiberRootPath p b z (reflTransReparam (TopCat.I.homeomorph t))
    exact h

private theorem constantSquareCoherenceStatement_proof :
    ConstantSquareCoherenceStatement.{u} := by
  intro X Y B s p q b h
  subst p
  let target : TopCat.homotopyFiber (s ≫ q) b ⟶
      TopCat.homotopyFiber q b :=
    TopCat.homotopyPullbackMap s (𝟙 (TopCat.of PUnit)) (𝟙 B)
      (by simp) (by simp)
  refine ⟨?_⟩
  apply homotopyFiberReparamHomotopy q b
    (homotopyFiberMapOfHomotopy s (s ≫ q) q b
      (strictSquareHomotopy s (s ≫ q) q rfl))
    target reflTransReparam reflTransReparam_continuous
    reflTransReparam_zero reflTransReparam_one
  · rw [homotopyFiberMapOfHomotopy_toTotal]
    simp [target]
  · rw [homotopyFiberMapOfHomotopy_path_map]
    apply TopCat.ext
    intro z
    apply ContinuousMap.ext
    intro t
    have hpoint :
        homotopyPointPath
            (strictSquareHomotopy s (s ≫ q) q rfl)
            (TopCat.homotopyFiberToTotal (s ≫ q) b z) =
          Path.refl ((s ≫ q)
            (TopCat.homotopyFiberToTotal (s ≫ q) b z)) := by
      apply Path.ext
      funext τ
      rfl
    have hreparam := congrArg
      (fun path : Path
          ((s ≫ q) (TopCat.homotopyFiberToTotal (s ≫ q) b z)) b =>
        path (TopCat.I.homeomorph t))
      (refl_trans_eq_reparam (fiberRootPath (s ≫ q) b z))
    change ((homotopyPointPath
          (strictSquareHomotopy s (s ≫ q) q rfl)
          (TopCat.homotopyFiberToTotal (s ≫ q) b z)).trans
        (fiberRootPath (s ≫ q) b z)) (TopCat.I.homeomorph t) =
      (target ≫ TopCat.homotopyFiberPath q b) z
        (TopCat.I.homeomorph.symm
          (blendReparam reflTransReparam 0 (TopCat.I.homeomorph t)))
    rw [blendReparam_zero, hpoint]
    have htarget : target ≫ TopCat.homotopyFiberPath q b =
        TopCat.homotopyFiberPath (s ≫ q) b := by
      simp [target]
    rw [htarget]
    change ((Path.refl
          ((s ≫ q) (TopCat.homotopyFiberToTotal (s ≫ q) b z))).trans
        (fiberRootPath (s ≫ q) b z)) (TopCat.I.homeomorph t) =
      fiberRootPath (s ≫ q) b z
        (reflTransReparam (TopCat.I.homeomorph t))
    exact hreparam

private theorem precomposeSquareHomotopy_pointPath
    {X Y Z B : TopCat.{u}} (s : X ⟶ Y) (t : Y ⟶ Z)
    (q : Y ⟶ B) (r : Z ⟶ B)
    (K : ContinuousMap.Homotopy (t ≫ r).hom q.hom) (x : X) :
    homotopyPointPath (precomposeSquareHomotopy s t q r K) x =
      homotopyPointPath K (s x) := by
  apply Path.ext
  funext τ
  rfl

private theorem compositeSquareHomotopy_pointPath
    {X Y Z B : TopCat.{u}}
    (s : X ⟶ Y) (t : Y ⟶ Z) (p : X ⟶ B)
    (q : Y ⟶ B) (r : Z ⟶ B)
    (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom)
    (K : ContinuousMap.Homotopy (t ≫ r).hom q.hom) (x : X) :
    homotopyPointPath (compositeSquareHomotopy s t p q r H K) x =
      (homotopyPointPath K (s x)).trans (homotopyPointPath H x) := by
  rw [compositeSquareHomotopy]
  apply Path.ext
  funext τ
  change ((precomposeSquareHomotopy s t q r K).trans H) (τ, x) = _
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split_ifs with hτ
  · change homotopyPointPath (precomposeSquareHomotopy s t q r K) x
        ⟨2 * τ, _⟩ = _
    rw [precomposeSquareHomotopy_pointPath]
  · rfl

private theorem compositionCoherenceStatement_proof :
    CompositionCoherenceStatement.{u} := by
  intro X Y Z B s t p q r b H K
  let first := homotopyFiberMapOfHomotopy s p q b H
  let second := homotopyFiberMapOfHomotopy t q r b K
  let direct := homotopyFiberMapOfHomotopy (s ≫ t) p r b
    (compositeSquareHomotopy s t p q r H K)
  have hDirectToSequential : ContinuousMap.Homotopy direct.hom
      (first ≫ second).hom := by
    apply homotopyFiberReparamHomotopy r b direct (first ≫ second)
      assocReparam assocReparam_continuous assocReparam_zero
        assocReparam_one
    · dsimp only [direct, first, second]
      simp [Category.assoc]
    · dsimp only [direct, first, second]
      rw [homotopyFiberMapOfHomotopy_path_map]
      apply TopCat.ext
      intro z
      apply ContinuousMap.ext
      intro τ
      let x := TopCat.homotopyFiberToTotal p b z
      let z₁ := homotopyFiberMapOfHomotopy s p q b H z
      have hTotal : TopCat.homotopyFiberToTotal q b z₁ = s x :=
        ConcreteCategory.congr_hom
          (homotopyFiberMapOfHomotopy_toTotal s p q b H) z
      have hSequential (v : TopCat.I.{u}) :
          TopCat.homotopyFiberPath r b
              (homotopyFiberMapOfHomotopy t q r b K z₁) v =
            ((homotopyPointPath K (s x)).trans
              ((homotopyPointPath H x).trans (fiberRootPath p b z)))
                (TopCat.I.homeomorph v) := by
        rw [homotopyFiberMapOfHomotopy_path]
        rw [Path.trans_apply]
        split_ifs with hv
        · rw [hTotal]
          rw [Path.trans_apply]
          simp only [hv]
          simp only [dite_true]
        · let w : unitInterval :=
            ⟨2 * TopCat.I.homeomorph v - 1,
              unitInterval.two_mul_sub_one_mem_iff.2
                ⟨(not_le.1 hv).le, (TopCat.I.homeomorph v).2.2⟩⟩
          have hFirst := homotopyFiberMapOfHomotopy_path
            s p q b H z (TopCat.I.homeomorph.symm w)
          rw [Path.trans_apply]
          simp only [hv]
          change TopCat.homotopyFiberPath q b z₁
              (TopCat.I.homeomorph.symm w) =
            ((homotopyPointPath H x).trans (fiberRootPath p b z)) w
          simpa [z₁, x, w] using hFirst
      have hAssoc := congrArg
        (fun path : Path (((t ≫ r) (s x))) b =>
          path (TopCat.I.homeomorph τ))
        (trans_assoc_eq_reparam
          (homotopyPointPath K (s x))
          (homotopyPointPath H x) (fiberRootPath p b z))
      change ((homotopyPointPath
            (compositeSquareHomotopy s t p q r H K) x).trans
          (fiberRootPath p b z)) (TopCat.I.homeomorph τ) =
        TopCat.homotopyFiberPath r b
          (homotopyFiberMapOfHomotopy t q r b K z₁)
          (TopCat.I.homeomorph.symm
            (blendReparam assocReparam 0 (TopCat.I.homeomorph τ)))
      rw [blendReparam_zero,
        compositeSquareHomotopy_pointPath]
      have hSeq := hSequential
        (TopCat.I.homeomorph.symm
          (assocReparam (TopCat.I.homeomorph τ)))
      rw [TopCat.I.homeomorph.apply_symm_apply] at hSeq
      exact hAssoc.trans hSeq.symm
  exact ⟨hDirectToSequential.symm⟩

/-! Private mapping-path replacement and fibration proof. -/

private abbrev mappingPath {Z B : TopCat.{u}} (r : Z ⟶ B) : TopCat.{u} :=
  pullback r (TopCat.pathEvalZero B)

private abbrev mappingPathProjection {Z B : TopCat.{u}} (r : Z ⟶ B) :
    mappingPath r ⟶ B :=
  pullback.snd r (TopCat.pathEvalZero B) ≫ TopCat.pathEvalOne B

private abbrev mappingPathToSource {Z B : TopCat.{u}} (r : Z ⟶ B) :
    mappingPath r ⟶ Z :=
  pullback.fst r (TopCat.pathEvalZero B)

private abbrev mappingPathPath {Z B : TopCat.{u}} (r : Z ⟶ B) :
    mappingPath r ⟶ TopCat.pathObject B :=
  pullback.snd r (TopCat.pathEvalZero B)

private noncomputable def mappingPathSection {Z B : TopCat.{u}}
    (r : Z ⟶ B) : Z ⟶ mappingPath r :=
  pullback.lift (𝟙 Z) (r ≫ TopCat.pathConstant B) (by simp)

@[reassoc (attr := simp)]
private theorem mappingPathSection_source {Z B : TopCat.{u}}
    (r : Z ⟶ B) :
    mappingPathSection r ≫ mappingPathToSource r = 𝟙 Z := by
  rw [mappingPathSection, pullback.lift_fst]

@[reassoc (attr := simp)]
private theorem mappingPathSection_path {Z B : TopCat.{u}}
    (r : Z ⟶ B) :
    mappingPathSection r ≫ mappingPathPath r =
      r ≫ TopCat.pathConstant B := by
  rw [mappingPathSection, pullback.lift_snd]

private def mappingPathScaleTime :
    C(unitInterval × TopCat.I.{u}, TopCat.I.{u}) where
  toFun z := TopCat.I.homeomorph.symm
    (z.1 * TopCat.I.homeomorph z.2)
  continuous_toFun := TopCat.I.homeomorph.symm.continuous.comp
    (Continuous.subtype_mk
      ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp
          (TopCat.I.homeomorph.continuous.comp continuous_snd))) _)

@[simp]
private theorem mappingPathScaleTime_zero (t : TopCat.I.{u}) :
    mappingPathScaleTime (0, t) = 0 := by
  apply TopCat.I.homeomorph.injective
  simp [mappingPathScaleTime]

@[simp]
private theorem mappingPathScaleTime_right_zero (s : unitInterval) :
    mappingPathScaleTime (s, 0) = 0 := by
  apply TopCat.I.homeomorph.injective
  simp [mappingPathScaleTime]

@[simp]
private theorem mappingPathScaleTime_one (t : TopCat.I.{u}) :
    mappingPathScaleTime (1, t) = t := by
  apply TopCat.I.homeomorph.injective
  simp [mappingPathScaleTime]

private noncomputable def mappingPathContractionPath
    {Z B : TopCat.{u}} (r : Z ⟶ B) :
    TopCat.of (unitInterval × mappingPath r) ⟶ TopCat.pathObject B :=
  TopCat.ofHom <| ContinuousMap.curry
    { toFun := fun z => mappingPathPath r z.1.2
        (mappingPathScaleTime (z.1.1, z.2))
      continuous_toFun := by fun_prop }

@[reassoc]
private theorem mappingPathContractionPath_zero
    {Z B : TopCat.{u}} (r : Z ⟶ B) :
    mappingPathContractionPath r ≫ TopCat.pathEvalZero B =
      (TopCat.ofHom
        { toFun := fun z : unitInterval × mappingPath r => z.2
          continuous_toFun := continuous_snd } ≫
        mappingPathToSource r) ≫ r := by
  ext z
  change mappingPathPath r z.2
      (mappingPathScaleTime (z.1, (0 : TopCat.I.{u}))) =
    r (mappingPathToSource r z.2)
  rw [mappingPathScaleTime_right_zero]
  have h := ConcreteCategory.congr_hom
    (pullback.condition : mappingPathToSource r ≫ r =
      mappingPathPath r ≫ TopCat.pathEvalZero B) z.2
  change r (mappingPathToSource r z.2) = mappingPathPath r z.2 0 at h
  exact h.symm

private noncomputable def mappingPathContractionMap
    {Z B : TopCat.{u}} (r : Z ⟶ B) :
    TopCat.of (unitInterval × mappingPath r) ⟶ mappingPath r :=
  pullback.lift
    (TopCat.ofHom
      { toFun := fun z : unitInterval × mappingPath r => z.2
        continuous_toFun := continuous_snd } ≫ mappingPathToSource r)
    (mappingPathContractionPath r)
    (mappingPathContractionPath_zero r).symm

private def mappingPathAtTime {Z B : TopCat.{u}} (r : Z ⟶ B)
    (t : unitInterval) :
    mappingPath r ⟶ TopCat.of (unitInterval × mappingPath r) :=
  TopCat.ofHom
    { toFun := fun z => (t, z)
      continuous_toFun := continuous_const.prodMk continuous_id }

private theorem mappingPathContractionMap_zero
    {Z B : TopCat.{u}} (r : Z ⟶ B) :
    mappingPathAtTime r 0 ≫ mappingPathContractionMap r =
      mappingPathToSource r ≫ mappingPathSection r := by
  apply pullback.hom_ext
  · rw [Category.assoc, mappingPathContractionMap, pullback.lift_fst]
    simp only [Category.assoc, mappingPathSection_source, Category.comp_id]
    apply TopCat.ext
    intro z
    rfl
  · rw [Category.assoc, mappingPathContractionMap, pullback.lift_snd,
      Category.assoc, mappingPathSection_path]
    ext z t
    change mappingPathPath r z (mappingPathScaleTime (0, t)) =
      TopCat.pathConstant B (r (mappingPathToSource r z)) t
    rw [mappingPathScaleTime_zero]
    have h := ConcreteCategory.congr_hom
      (pullback.condition : mappingPathToSource r ≫ r =
        mappingPathPath r ≫ TopCat.pathEvalZero B) z
    change r (mappingPathToSource r z) = mappingPathPath r z 0 at h
    simpa [TopCat.pathConstant] using h.symm

private theorem mappingPathContractionMap_one
    {Z B : TopCat.{u}} (r : Z ⟶ B) :
    mappingPathAtTime r 1 ≫ mappingPathContractionMap r = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, mappingPathContractionMap, pullback.lift_fst,
      Category.id_comp]
    apply TopCat.ext
    intro z
    rfl
  · rw [Category.assoc, mappingPathContractionMap, pullback.lift_snd,
      Category.id_comp]
    ext z t
    simp [mappingPathAtTime, mappingPathContractionPath]

private noncomputable def mappingPathSourceHomotopy
    {Z B : TopCat.{u}} (r : Z ⟶ B) :
    ContinuousMap.Homotopy
      (mappingPathToSource r ≫ mappingPathSection r).hom
      (𝟙 (mappingPath r) : mappingPath r ⟶ mappingPath r).hom :=
  ContinuousMap.Homotopy.mk (mappingPathContractionMap r).hom
    (fun z => by
      have h := ConcreteCategory.congr_hom
        (mappingPathContractionMap_zero r) z
      simpa [mappingPathAtTime] using h)
    (fun z => by
      have h := ConcreteCategory.congr_hom
        (mappingPathContractionMap_one r) z
      simpa [mappingPathAtTime] using h)

private noncomputable def mappingPathSourceHomotopyEquiv
    {Z B : TopCat.{u}} (r : Z ⟶ B) :
    ContinuousMap.HomotopyEquiv (mappingPath r) Z where
  toFun := (mappingPathToSource r).hom
  invFun := (mappingPathSection r).hom
  left_inv := ⟨mappingPathSourceHomotopy r⟩
  right_inv := by
    rw [show (mappingPathToSource r).hom.comp (mappingPathSection r).hom =
      (mappingPathSection r ≫ mappingPathToSource r).hom by rfl,
      mappingPathSection_source]
    exact ⟨ContinuousMap.Homotopy.refl _⟩

private theorem mappingPathToSource_mem_weakHomotopyEquivalences
    {Z B : TopCat.{u}} (r : Z ⟶ B) :
    TopCat.weakHomotopyEquivalences (mappingPathToSource r) :=
  TopCat.homotopyEquiv_toFun_mem (mappingPathSourceHomotopyEquiv r)

private def mappingPathRootPath {Z B : TopCat.{u}} (r : Z ⟶ B)
    (z : mappingPath r) :
    Path (r (mappingPathToSource r z)) (mappingPathProjection r z) where
  toFun t := mappingPathPath r z (TopCat.I.homeomorph.symm t)
  continuous_toFun := (mappingPathPath r z).continuous.comp
    TopCat.I.homeomorph.symm.continuous
  source' := by
    have h := ConcreteCategory.congr_hom
      (pullback.condition : mappingPathToSource r ≫ r =
        mappingPathPath r ≫ TopCat.pathEvalZero B) z
    have hZero : TopCat.I.homeomorph.symm (0 : unitInterval) =
        (0 : TopCat.I.{u}) := by
      apply TopCat.I.homeomorph.injective
      simp
    rw [hZero]
    change r (mappingPathToSource r z) = mappingPathPath r z 0 at h
    exact h.symm
  target' := by
    have hOne : TopCat.I.homeomorph.symm (1 : unitInterval) =
        (1 : TopCat.I.{u}) := by
      apply TopCat.I.homeomorph.injective
      simp
    change mappingPathPath r z (TopCat.I.homeomorph.symm 1) = _
    rw [hOne]
    rfl

private theorem mappingPathRootPath_continuous_family
    {Z B : TopCat.{u}} (r : Z ⟶ B) :
    Continuous (fun z : mappingPath r × unitInterval =>
      mappingPathRootPath r z.1 z.2) := by
  exact continuous_eval.comp
    (((mappingPathPath r).hom.continuous.comp continuous_fst).prodMk
      (TopCat.I.homeomorph.symm.continuous.comp continuous_snd))

private def prependMappingPath
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    mappingPath p ⟶ TopCat.pathObject B :=
  TopCat.ofHom <| ContinuousMap.curry
    { toFun := fun z =>
        ((homotopyPointPath H (mappingPathToSource p z.1)).trans
          (mappingPathRootPath p z.1)) (TopCat.I.homeomorph z.2)
      continuous_toFun := by
        have hH : Continuous (fun z : mappingPath p × unitInterval =>
            homotopyPointPath H (mappingPathToSource p z.1) z.2) :=
          (homotopyPointPath_continuous_family H).comp
            (((mappingPathToSource p).hom.continuous.comp
              continuous_fst).prodMk continuous_snd)
        have htrans := Path.trans_continuous_family
          (fun z : mappingPath p =>
            homotopyPointPath H (mappingPathToSource p z)) hH
          (mappingPathRootPath p)
          (mappingPathRootPath_continuous_family p)
        exact htrans.comp
          (continuous_fst.prodMk
            (TopCat.I.homeomorph.continuous.comp continuous_snd)) }

@[reassoc]
private theorem prependMappingPath_evalZero
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    prependMappingPath s p q H ≫ TopCat.pathEvalZero B =
      (mappingPathToSource p ≫ s) ≫ q := by
  apply TopCat.ext
  intro z
  change ((homotopyPointPath H (mappingPathToSource p z)).trans
      (mappingPathRootPath p z))
      (TopCat.I.homeomorph (0 : TopCat.I.{u})) = _
  rw [TopCat.I.homeomorph_zero]
  exact ((homotopyPointPath H (mappingPathToSource p z)).trans
    (mappingPathRootPath p z)).source'

@[reassoc]
private theorem prependMappingPath_evalOne
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    prependMappingPath s p q H ≫ TopCat.pathEvalOne B =
      mappingPathProjection p := by
  apply TopCat.ext
  intro z
  change ((homotopyPointPath H (mappingPathToSource p z)).trans
      (mappingPathRootPath p z))
      (TopCat.I.homeomorph (1 : TopCat.I.{u})) = _
  rw [TopCat.I.homeomorph_one]
  exact ((homotopyPointPath H (mappingPathToSource p z)).trans
    (mappingPathRootPath p z)).target'

private noncomputable def mappingPathMapOfHomotopy
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    mappingPath p ⟶ mappingPath q :=
  pullback.lift (mappingPathToSource p ≫ s)
    (prependMappingPath s p q H)
    (prependMappingPath_evalZero s p q H).symm

@[reassoc (attr := simp)]
private theorem mappingPathMapOfHomotopy_source
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    mappingPathMapOfHomotopy s p q H ≫ mappingPathToSource q =
      mappingPathToSource p ≫ s := by
  rw [mappingPathMapOfHomotopy, pullback.lift_fst]

@[reassoc (attr := simp)]
private theorem mappingPathMapOfHomotopy_path
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    mappingPathMapOfHomotopy s p q H ≫ mappingPathPath q =
      prependMappingPath s p q H := by
  rw [mappingPathMapOfHomotopy, pullback.lift_snd]

@[reassoc]
private theorem mappingPathMapOfHomotopy_projection
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    mappingPathMapOfHomotopy s p q H ≫ mappingPathProjection q =
      mappingPathProjection p := by
  rw [mappingPathProjection, ← Category.assoc,
    mappingPathMapOfHomotopy_path, prependMappingPath_evalOne]

private theorem mappingPathMapOfHomotopy_mem_weakHomotopyEquivalences
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom)
    (hs : TopCat.weakHomotopyEquivalences s) :
    TopCat.weakHomotopyEquivalences
      (mappingPathMapOfHomotopy s p q H) := by
  have hp := mappingPathToSource_mem_weakHomotopyEquivalences p
  have hq := mappingPathToSource_mem_weakHomotopyEquivalences q
  have hcomp : TopCat.weakHomotopyEquivalences
      (mappingPathMapOfHomotopy s p q H ≫ mappingPathToSource q) := by
    rw [mappingPathMapOfHomotopy_source]
    exact TopCat.weakHomotopyEquivalences.comp_mem _ _ hp hs
  exact TopCat.weakHomotopyEquivalences.of_postcomp _ _ hq hcomp

private noncomputable def mappingPathPair {Z B : TopCat.{u}}
    (r : Z ⟶ B) : mappingPath r ⟶ Z ⨯ B :=
  Limits.prod.lift (mappingPathToSource r) (mappingPathProjection r)

@[reassoc (attr := simp)]
private theorem mappingPathPair_fst {Z B : TopCat.{u}} (r : Z ⟶ B) :
    mappingPathPair r ≫ Limits.prod.fst = mappingPathToSource r := by
  simp [mappingPathPair]

@[reassoc (attr := simp)]
private theorem mappingPathPair_snd {Z B : TopCat.{u}} (r : Z ⟶ B) :
    mappingPathPair r ≫ Limits.prod.snd = mappingPathProjection r := by
  simp [mappingPathPair]

private theorem mappingPathPair_condition {Z B : TopCat.{u}}
    (r : Z ⟶ B) :
    mappingPathPair r ≫ Limits.prod.map r (𝟙 B) =
      mappingPathPath r ≫ TopCat.pathEndpoints B := by
  apply Limits.prod.hom_ext
  · simpa [Category.assoc, TopCat.pathEndpoints] using
      (pullback.condition : mappingPathToSource r ≫ r =
        mappingPathPath r ≫ TopCat.pathEvalZero B)
  · simp [Category.assoc, mappingPathProjection, TopCat.pathEndpoints]

private theorem mappingPathPair_isPullback {Z B : TopCat.{u}}
    (r : Z ⟶ B) :
    IsPullback (mappingPathPair r) (mappingPathPath r)
      (Limits.prod.map r (𝟙 B)) (TopCat.pathEndpoints B) := by
  let hcond := mappingPathPair_condition r
  refine { w := hcond, isLimit' := ?_ }
  refine ⟨PullbackCone.IsLimit.mk hcond
    (fun s => pullback.lift (s.fst ≫ Limits.prod.fst) s.snd ?_)
    (fun s => ?_)
    (fun s => by rw [pullback.lift_snd])
    (fun s m h₁ h₂ => ?_)⟩
  · have h := congrArg (fun k => k ≫ Limits.prod.fst) s.condition
    simpa [Category.assoc, TopCat.pathEndpoints] using h
  · apply Limits.prod.hom_ext
    · simp only [Category.assoc, mappingPathPair_fst]
      rw [pullback.lift_fst]
    · have h := congrArg (fun k => k ≫ Limits.prod.snd) s.condition
      simp only [Category.assoc, mappingPathPair_snd,
        mappingPathProjection]
      rw [← Category.assoc, pullback.lift_snd]
      simpa [Category.assoc, TopCat.pathEndpoints] using h.symm
  · apply pullback.hom_ext
    · have h := congrArg (fun k => k ≫ Limits.prod.fst) h₁
      rw [pullback.lift_fst]
      simpa [Category.assoc] using h
    · rw [pullback.lift_snd]
      exact h₂

private theorem selectedTopCat_isFibrant (X : TopCat.{u}) :
    let _ : ModelCategory TopCat.{u} := TopCat.modelCategory
    IsFibrant X := by
  let _ : ModelCategory TopCat.{u} := TopCat.modelCategory
  let _ : CategoryWithFibrations SSet.{u} :=
    SSet.modelCategoryQuillen.instCategoryWithFibrations
  rw [isFibrant_iff]
  rw [fibration_iff]
  change TopCat.realizedHornInclusions.{u}.rlp (terminal.from X)
  rw [TopCat.hornRLP_iff_toSSet_mem_J_rlp]
  apply (SSet.modelCategoryQuillen.fibration_iff
    (TopCat.toSSet.map (terminal.from X))).mp
  rw [← isFibrant_iff_of_isTerminal _
    (IsTerminal.isTerminalObj TopCat.toSSet _ terminalIsTerminal)]
  exact TopCat.toSSet_obj_kanComplex X

private theorem mappingPathPair_fibration_of_endpoint
    {Z B : TopCat.{u}} (r : Z ⟶ B)
    (hEndpoint :
      let _ : ModelCategory TopCat.{u} := TopCat.modelCategory
      Fibration (TopCat.pathEndpoints B)) :
    let _ : ModelCategory TopCat.{u} := TopCat.modelCategory
    Fibration (mappingPathPair r) := by
  let _ : ModelCategory TopCat.{u} := TopCat.modelCategory
  let _ : Fibration (TopCat.pathEndpoints B) := hEndpoint
  rw [fibration_iff]
  exact MorphismProperty.of_isPullback (mappingPathPair_isPullback r).flip
    ((fibration_iff _).1 (inferInstance : Fibration (TopCat.pathEndpoints B)))

private theorem mappingPathProjection_fibration_of_endpoint
    {Z B : TopCat.{u}} (r : Z ⟶ B)
    (hEndpoint :
      let _ : ModelCategory TopCat.{u} := TopCat.modelCategory
      Fibration (TopCat.pathEndpoints B)) :
    let _ : ModelCategory TopCat.{u} := TopCat.modelCategory
    Fibration (mappingPathProjection r) := by
  let _ : ModelCategory TopCat.{u} := TopCat.modelCategory
  let _ : Fibration (mappingPathPair r) :=
    mappingPathPair_fibration_of_endpoint r hEndpoint
  let _ : IsFibrant Z := selectedTopCat_isFibrant Z
  have hfactor : mappingPathProjection r =
      mappingPathPair r ≫ (Limits.prod.snd : Z ⨯ B ⟶ B) := by
    simp
  rw [hfactor]
  infer_instance

private abbrev homotopyFiberBaseProjection
    {E B : TopCat.{u}} (e : E ⟶ B) (b : B) :
    TopCat.homotopyFiber e b ⟶ E ⨯ TopCat.of PUnit :=
  pullback.fst (Limits.prod.map e (TopCat.const b))
    (TopCat.pathEndpoints B)

private noncomputable def mappingPathHomotopyFiberMap
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    TopCat.homotopyFiber (mappingPathProjection p) b ⟶
      TopCat.homotopyFiber (mappingPathProjection q) b :=
  TopCat.homotopyPullbackMap
    (mappingPathMapOfHomotopy s p q H) (𝟙 (TopCat.of PUnit)) (𝟙 B)
    (by simpa using (mappingPathMapOfHomotopy_projection s p q H).symm)
    (by simp)

@[reassoc (attr := simp)]
private theorem mappingPathHomotopyFiberMap_base
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    mappingPathHomotopyFiberMap s p q b H ≫
        homotopyFiberBaseProjection (mappingPathProjection q) b =
      homotopyFiberBaseProjection (mappingPathProjection p) b ≫
        Limits.prod.map (mappingPathMapOfHomotopy s p q H)
          (𝟙 (TopCat.of PUnit)) := by
  rw [mappingPathHomotopyFiberMap, TopCat.homotopyPullbackMap,
    pullback.lift_fst]

@[reassoc (attr := simp)]
private theorem mappingPathHomotopyFiberMap_path
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    mappingPathHomotopyFiberMap s p q b H ≫
        TopCat.homotopyFiberPath (mappingPathProjection q) b =
      TopCat.homotopyFiberPath (mappingPathProjection p) b := by
  rw [mappingPathHomotopyFiberMap, TopCat.homotopyPullbackMap_path]
  simp [TopCat.pathObjectMap_id]

private theorem mappingPathHomotopyFiberMap_isPullback
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    IsPullback
      (mappingPathHomotopyFiberMap s p q b H)
      (homotopyFiberBaseProjection (mappingPathProjection p) b)
      (homotopyFiberBaseProjection (mappingPathProjection q) b)
      (Limits.prod.map (mappingPathMapOfHomotopy s p q H)
        (𝟙 (TopCat.of PUnit))) := by
  have hbase : Limits.prod.map (mappingPathProjection p)
        (TopCat.const (X := TopCat.of PUnit) b) =
      Limits.prod.map (mappingPathMapOfHomotopy s p q H)
          (𝟙 (TopCat.of PUnit)) ≫
        Limits.prod.map (mappingPathProjection q)
          (TopCat.const (X := TopCat.of PUnit) b) := by
    apply Limits.prod.hom_ext
    · simpa only [Category.assoc, Limits.prod.map_fst,
        Limits.prod.map_fst_assoc] using
        congrArg (fun k => Limits.prod.fst ≫ k)
          (mappingPathMapOfHomotopy_projection s p q H).symm
    · simp only [Category.assoc, Limits.prod.map_snd,
        Limits.prod.map_snd_assoc]
      rw [← Category.assoc, Category.comp_id]
  have hcond := mappingPathHomotopyFiberMap_base s p q b H
  have liftCond : ∀ c : PullbackCone
      (homotopyFiberBaseProjection (mappingPathProjection q) b)
      (Limits.prod.map (mappingPathMapOfHomotopy s p q H)
        (𝟙 (TopCat.of PUnit))),
      c.snd ≫ Limits.prod.map (mappingPathProjection p)
          (TopCat.const (X := TopCat.of PUnit) b) =
        (c.fst ≫ TopCat.homotopyFiberPath (mappingPathProjection q) b) ≫
          TopCat.pathEndpoints B := by
    intro c
    calc
      c.snd ≫ Limits.prod.map (mappingPathProjection p)
          (TopCat.const (X := TopCat.of PUnit) b) =
        c.snd ≫
          (Limits.prod.map (mappingPathMapOfHomotopy s p q H)
              (𝟙 (TopCat.of PUnit)) ≫
            Limits.prod.map (mappingPathProjection q)
              (TopCat.const (X := TopCat.of PUnit) b)) :=
        congrArg (c.snd ≫ ·) hbase
      _ = (c.snd ≫ Limits.prod.map
          (mappingPathMapOfHomotopy s p q H)
          (𝟙 (TopCat.of PUnit))) ≫
            Limits.prod.map (mappingPathProjection q)
              (TopCat.const (X := TopCat.of PUnit) b) :=
        (Category.assoc _ _ _).symm
      _ = (c.fst ≫ homotopyFiberBaseProjection
          (mappingPathProjection q) b) ≫
            Limits.prod.map (mappingPathProjection q)
              (TopCat.const (X := TopCat.of PUnit) b) :=
        congrArg (· ≫ Limits.prod.map (mappingPathProjection q)
          (TopCat.const (X := TopCat.of PUnit) b)) c.condition.symm
      _ = c.fst ≫ (homotopyFiberBaseProjection
          (mappingPathProjection q) b ≫
            Limits.prod.map (mappingPathProjection q)
              (TopCat.const (X := TopCat.of PUnit) b)) :=
        Category.assoc _ _ _
      _ = c.fst ≫ (TopCat.homotopyFiberPath
          (mappingPathProjection q) b ≫ TopCat.pathEndpoints B) :=
        congrArg (c.fst ≫ ·) pullback.condition
      _ = (c.fst ≫ TopCat.homotopyFiberPath
          (mappingPathProjection q) b) ≫ TopCat.pathEndpoints B :=
        (Category.assoc _ _ _).symm
  refine { w := hcond, isLimit' := ?_ }
  refine ⟨PullbackCone.IsLimit.mk hcond
    (fun c => pullback.lift c.snd
      (c.fst ≫ TopCat.homotopyFiberPath (mappingPathProjection q) b)
      (liftCond c))
    (fun c => ?_)
    (fun c => by rw [pullback.lift_fst])
    (fun c m h₁ h₂ => ?_)⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, mappingPathHomotopyFiberMap_base]
      rw [← Category.assoc, pullback.lift_fst]
      exact c.condition.symm
    · rw [Category.assoc, mappingPathHomotopyFiberMap_path]
      rw [pullback.lift_snd]
  · apply pullback.hom_ext
    · rw [pullback.lift_fst]
      exact h₂
    · calc
        m ≫ TopCat.homotopyFiberPath (mappingPathProjection p) b =
            (m ≫ mappingPathHomotopyFiberMap s p q b H) ≫
              TopCat.homotopyFiberPath (mappingPathProjection q) b := by
          rw [Category.assoc, mappingPathHomotopyFiberMap_path]
        _ = c.fst ≫ TopCat.homotopyFiberPath
              (mappingPathProjection q) b := by rw [h₁]
        _ = pullback.lift c.snd
              (c.fst ≫ TopCat.homotopyFiberPath
                (mappingPathProjection q) b) _ ≫
              TopCat.homotopyFiberPath (mappingPathProjection p) b := by
          rw [pullback.lift_snd]

private theorem mappingPathHomotopyFiberMap_mem_weakHomotopyEquivalences
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom)
    (hs : TopCat.weakHomotopyEquivalences s)
    (hEndpoint :
      let _ : ModelCategory TopCat.{u} := TopCat.modelCategory
      Fibration (TopCat.pathEndpoints B)) :
    TopCat.weakHomotopyEquivalences
      (mappingPathHomotopyFiberMap s p q b H) := by
  let _ : ModelCategory TopCat.{u} := TopCat.modelCategory
  let _ : Fibration (TopCat.pathEndpoints B) := hEndpoint
  let hright := IsPullback.of_hasPullback
    (Limits.prod.map (mappingPathProjection q)
      (TopCat.const (X := TopCat.of PUnit) b))
    (TopCat.pathEndpoints B)
  let _ : Fibration
      (homotopyFiberBaseProjection (mappingPathProjection q) b) :=
    (fibration_iff _).2 (MorphismProperty.of_isPullback hright.flip
      ((fibration_iff _).1
        (inferInstance : Fibration (TopCat.pathEndpoints B))))
  have hw := mappingPathMapOfHomotopy_mem_weakHomotopyEquivalences
    s p q H hs
  have hprod : TopCat.weakHomotopyEquivalences
      (Limits.prod.map (mappingPathMapOfHomotopy s p q H)
        (𝟙 (TopCat.of PUnit))) :=
    TopCat.weakHomotopyEquivalences.prodMap hw
      (TopCat.weakHomotopyEquivalences.id_mem _)
  let _ : WeakEquivalence
      (Limits.prod.map (mappingPathMapOfHomotopy s p q H)
        (𝟙 (TopCat.of PUnit))) :=
    (weakEquivalence_iff _).2 hprod
  let _ : IsRightProper TopCat.{u} := TopCat.modelCategory.rightProper
  let _ : WeakEquivalence (mappingPathHomotopyFiberMap s p q b H) :=
    IsRightProper.weakEquivalence_of_isPullback
      (mappingPathHomotopyFiberMap_isPullback s p q b H).flip
  exact (weakEquivalence_iff
    (mappingPathHomotopyFiberMap s p q b H)).1
      (inferInstance : WeakEquivalence
        (mappingPathHomotopyFiberMap s p q b H))

private abbrev mappingPathStrictFiber
    {Z B : TopCat.{u}} (r : Z ⟶ B) (b : B) : TopCat.{u} :=
  pullback (mappingPathProjection r)
    (TopCat.const (X := TopCat.of PUnit) b)

private noncomputable def mappingPathStrictFiberToHomotopyFiber
    {Z B : TopCat.{u}} (r : Z ⟶ B) (b : B) :
    mappingPathStrictFiber r b ⟶ TopCat.homotopyFiber r b :=
  pullback.lift
    (Limits.prod.lift
      (pullback.fst (mappingPathProjection r)
        (TopCat.const (X := TopCat.of PUnit) b) ≫
        mappingPathToSource r)
      (pullback.snd (mappingPathProjection r)
        (TopCat.const (X := TopCat.of PUnit) b)))
    (pullback.fst (mappingPathProjection r)
      (TopCat.const (X := TopCat.of PUnit) b) ≫
      mappingPathPath r)
    (by
      apply Limits.prod.hom_ext
      · let sf := pullback.fst (mappingPathProjection r)
          (TopCat.const (X := TopCat.of PUnit) b)
        have h := congrArg (fun k => sf ≫ k)
          (pullback.condition : mappingPathToSource r ≫ r =
            mappingPathPath r ≫ TopCat.pathEvalZero B)
        simpa [TopCat.pathEndpoints, Category.assoc] using h
      · have h :=
          (pullback.condition :
            pullback.fst (mappingPathProjection r)
                (TopCat.const (X := TopCat.of PUnit) b) ≫
                mappingPathProjection r =
              pullback.snd (mappingPathProjection r)
                  (TopCat.const (X := TopCat.of PUnit) b) ≫
                TopCat.const (X := TopCat.of PUnit) b)
        simpa [TopCat.pathEndpoints, mappingPathProjection,
          Category.assoc] using h.symm)

@[reassoc (attr := simp)]
private theorem mappingPathStrictFiberToHomotopyFiber_total
    {Z B : TopCat.{u}} (r : Z ⟶ B) (b : B) :
    mappingPathStrictFiberToHomotopyFiber r b ≫
        TopCat.homotopyFiberToTotal r b =
      pullback.fst (mappingPathProjection r)
          (TopCat.const (X := TopCat.of PUnit) b) ≫
        mappingPathToSource r := by
  rw [mappingPathStrictFiberToHomotopyFiber,
    TopCat.homotopyFiberToTotal, ← Category.assoc, pullback.lift_fst]
  simp

@[reassoc (attr := simp)]
private theorem mappingPathStrictFiberToHomotopyFiber_unit
    {Z B : TopCat.{u}} (r : Z ⟶ B) (b : B) :
    mappingPathStrictFiberToHomotopyFiber r b ≫
        TopCat.homotopyPullbackRight r
          (TopCat.const (X := TopCat.of PUnit) b) =
      pullback.snd (mappingPathProjection r)
        (TopCat.const (X := TopCat.of PUnit) b) := by
  rw [mappingPathStrictFiberToHomotopyFiber,
    TopCat.homotopyPullbackRight, ← Category.assoc, pullback.lift_fst]
  simp

@[reassoc (attr := simp)]
private theorem mappingPathStrictFiberToHomotopyFiber_path
    {Z B : TopCat.{u}} (r : Z ⟶ B) (b : B) :
    mappingPathStrictFiberToHomotopyFiber r b ≫
        TopCat.homotopyFiberPath r b =
      pullback.fst (mappingPathProjection r)
          (TopCat.const (X := TopCat.of PUnit) b) ≫
        mappingPathPath r := by
  rw [mappingPathStrictFiberToHomotopyFiber,
    TopCat.homotopyFiberPath, pullback.lift_snd]

private noncomputable def homotopyFiberToMappingPath
    {Z B : TopCat.{u}} (r : Z ⟶ B) (b : B) :
    TopCat.homotopyFiber r b ⟶ mappingPath r :=
  pullback.lift (TopCat.homotopyFiberToTotal r b)
    (TopCat.homotopyFiberPath r b)
    (TopCat.homotopyPullbackPath_evalZero r
      (TopCat.const (X := TopCat.of PUnit) b)).symm

@[reassoc (attr := simp)]
private theorem homotopyFiberToMappingPath_source
    {Z B : TopCat.{u}} (r : Z ⟶ B) (b : B) :
    homotopyFiberToMappingPath r b ≫ mappingPathToSource r =
      TopCat.homotopyFiberToTotal r b := by
  rw [homotopyFiberToMappingPath, pullback.lift_fst]

@[reassoc (attr := simp)]
private theorem homotopyFiberToMappingPath_path
    {Z B : TopCat.{u}} (r : Z ⟶ B) (b : B) :
    homotopyFiberToMappingPath r b ≫ mappingPathPath r =
      TopCat.homotopyFiberPath r b := by
  rw [homotopyFiberToMappingPath, pullback.lift_snd]

private noncomputable def homotopyFiberToMappingPathStrictFiber
    {Z B : TopCat.{u}} (r : Z ⟶ B) (b : B) :
    TopCat.homotopyFiber r b ⟶ mappingPathStrictFiber r b :=
  pullback.lift (homotopyFiberToMappingPath r b)
    (TopCat.homotopyPullbackRight r
      (TopCat.const (X := TopCat.of PUnit) b))
    (by
      rw [mappingPathProjection, ← Category.assoc,
        homotopyFiberToMappingPath_path,
        TopCat.homotopyPullbackPath_evalOne])

@[reassoc (attr := simp)]
private theorem homotopyFiberToMappingPathStrictFiber_fst
    {Z B : TopCat.{u}} (r : Z ⟶ B) (b : B) :
    homotopyFiberToMappingPathStrictFiber r b ≫
        pullback.fst (mappingPathProjection r)
          (TopCat.const (X := TopCat.of PUnit) b) =
      homotopyFiberToMappingPath r b := by
  rw [homotopyFiberToMappingPathStrictFiber, pullback.lift_fst]

@[reassoc (attr := simp)]
private theorem homotopyFiberToMappingPathStrictFiber_snd
    {Z B : TopCat.{u}} (r : Z ⟶ B) (b : B) :
    homotopyFiberToMappingPathStrictFiber r b ≫
        pullback.snd (mappingPathProjection r)
          (TopCat.const (X := TopCat.of PUnit) b) =
      TopCat.homotopyPullbackRight r
        (TopCat.const (X := TopCat.of PUnit) b) := by
  rw [homotopyFiberToMappingPathStrictFiber, pullback.lift_snd]

private theorem mappingPathStrictFiber_inverse_fst
    {Z B : TopCat.{u}} (r : Z ⟶ B) (b : B) :
    mappingPathStrictFiberToHomotopyFiber r b ≫
        homotopyFiberToMappingPath r b =
      pullback.fst (mappingPathProjection r)
        (TopCat.const (X := TopCat.of PUnit) b) := by
  apply pullback.hom_ext
  · simp
  · simp

private noncomputable def mappingPathStrictFiberIso
    {Z B : TopCat.{u}} (r : Z ⟶ B) (b : B) :
    mappingPathStrictFiber r b ≅ TopCat.homotopyFiber r b where
  hom := mappingPathStrictFiberToHomotopyFiber r b
  inv := homotopyFiberToMappingPathStrictFiber r b
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, homotopyFiberToMappingPathStrictFiber_fst,
        mappingPathStrictFiber_inverse_fst, Category.id_comp]
    · rw [Category.assoc, homotopyFiberToMappingPathStrictFiber_snd,
        mappingPathStrictFiberToHomotopyFiber_unit, Category.id_comp]
  inv_hom_id := by
    apply TopCat.homotopyPullback_hom_ext
    · simp
    · simp
    · simp

private noncomputable def mappingPathStrictFiberMap
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    mappingPathStrictFiber p b ⟶ mappingPathStrictFiber q b :=
  pullback.lift
    (pullback.fst (mappingPathProjection p)
      (TopCat.const (X := TopCat.of PUnit) b) ≫
      mappingPathMapOfHomotopy s p q H)
    (pullback.snd (mappingPathProjection p)
      (TopCat.const (X := TopCat.of PUnit) b))
    (by
      rw [Category.assoc, mappingPathMapOfHomotopy_projection]
      exact pullback.condition)

@[reassoc (attr := simp)]
private theorem mappingPathStrictFiberMap_fst
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    mappingPathStrictFiberMap s p q b H ≫
        pullback.fst (mappingPathProjection q)
          (TopCat.const (X := TopCat.of PUnit) b) =
      pullback.fst (mappingPathProjection p)
          (TopCat.const (X := TopCat.of PUnit) b) ≫
        mappingPathMapOfHomotopy s p q H := by
  rw [mappingPathStrictFiberMap, pullback.lift_fst]

@[reassoc (attr := simp)]
private theorem mappingPathStrictFiberMap_snd
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    mappingPathStrictFiberMap s p q b H ≫
        pullback.snd (mappingPathProjection q)
          (TopCat.const (X := TopCat.of PUnit) b) =
      pullback.snd (mappingPathProjection p)
        (TopCat.const (X := TopCat.of PUnit) b) := by
  rw [mappingPathStrictFiberMap, pullback.lift_snd]

private theorem strictFiberComparison_naturality
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    mappingPathStrictFiberMap s p q b H ≫
        TopCat.strictFiberToHomotopyFiber (mappingPathProjection q) b =
      TopCat.strictFiberToHomotopyFiber (mappingPathProjection p) b ≫
        mappingPathHomotopyFiberMap s p q b H := by
  apply TopCat.homotopyPullback_hom_ext
  · simp
  · apply TopCat.isTerminalPUnit.hom_ext
  · simp

private theorem mappingPathStrictFiberMap_mem_weakHomotopyEquivalences
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom)
    (hs : TopCat.weakHomotopyEquivalences s)
    (hEndpoint :
      let _ : ModelCategory TopCat.{u} := TopCat.modelCategory
      Fibration (TopCat.pathEndpoints B)) :
    TopCat.weakHomotopyEquivalences
      (mappingPathStrictFiberMap s p q b H) := by
  let _ : ModelCategory TopCat.{u} := TopCat.modelCategory
  let _ : Fibration (mappingPathProjection p) :=
    mappingPathProjection_fibration_of_endpoint p hEndpoint
  let _ : Fibration (mappingPathProjection q) :=
    mappingPathProjection_fibration_of_endpoint q hEndpoint
  have hjp := TopCat.strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences
    (mappingPathProjection p) b
  have hjq := TopCat.strictFiberToHomotopyFiber_mem_weakHomotopyEquivalences
    (mappingPathProjection q) b
  have hh := mappingPathHomotopyFiberMap_mem_weakHomotopyEquivalences
    s p q b H hs hEndpoint
  have hcomp : TopCat.weakHomotopyEquivalences
      (mappingPathStrictFiberMap s p q b H ≫
        TopCat.strictFiberToHomotopyFiber (mappingPathProjection q) b) := by
    rw [strictFiberComparison_naturality]
    exact TopCat.weakHomotopyEquivalences.comp_mem _ _ hjp hh
  exact TopCat.weakHomotopyEquivalences.of_postcomp _ _ hjq hcomp

private theorem homotopyFiberToMappingPath_prepend
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    homotopyFiberToMappingPath p b ≫ prependMappingPath s p q H =
      prependHomotopyFiberPath s p q b H := by
  apply TopCat.ext
  intro z
  apply ContinuousMap.ext
  intro t
  change ((homotopyPointPath H
      (mappingPathToSource p (homotopyFiberToMappingPath p b z))).trans
        (mappingPathRootPath p (homotopyFiberToMappingPath p b z)))
          (TopCat.I.homeomorph t) =
    ((homotopyPointPath H (TopCat.homotopyFiberToTotal p b z)).trans
      (fiberRootPath p b z)) (TopCat.I.homeomorph t)
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs with ht
  · have hx := ConcreteCategory.congr_hom
      (homotopyFiberToMappingPath_source p b) z
    exact congrArg
      (fun x => H
        (⟨2 * (TopCat.I.homeomorph t),
          (unitInterval.mul_pos_mem_iff zero_lt_two).2
            ⟨(TopCat.I.homeomorph t).2.1, ht⟩⟩, x)) hx
  · have hp := ConcreteCategory.congr_hom
      (homotopyFiberToMappingPath_path p b) z
    exact congrArg
      (fun gamma => gamma
        (TopCat.I.homeomorph.symm
          ⟨2 * (TopCat.I.homeomorph t) - 1,
            unitInterval.two_mul_sub_one_mem_iff.2
              ⟨(not_le.1 ht).le, (TopCat.I.homeomorph t).2.2⟩⟩)) hp

private theorem mappingPathStrictFiberIso_naturality
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    (mappingPathStrictFiberIso p b).inv ≫
          mappingPathStrictFiberMap s p q b H ≫
          (mappingPathStrictFiberIso q b).hom =
      homotopyFiberMapOfHomotopy s p q b H := by
  dsimp [mappingPathStrictFiberIso]
  apply TopCat.homotopyPullback_hom_ext
  · change (homotopyFiberToMappingPathStrictFiber p b ≫
        mappingPathStrictFiberMap s p q b H ≫
        mappingPathStrictFiberToHomotopyFiber q b) ≫
          TopCat.homotopyFiberToTotal q b =
        homotopyFiberMapOfHomotopy s p q b H ≫
          TopCat.homotopyFiberToTotal q b
    simp [Category.assoc]
  · apply TopCat.isTerminalPUnit.hom_ext
  · change (homotopyFiberToMappingPathStrictFiber p b ≫
        mappingPathStrictFiberMap s p q b H ≫
        mappingPathStrictFiberToHomotopyFiber q b) ≫
          TopCat.homotopyFiberPath q b =
        homotopyFiberMapOfHomotopy s p q b H ≫
          TopCat.homotopyFiberPath q b
    calc
      _ = (homotopyFiberToMappingPathStrictFiber p b ≫
            mappingPathStrictFiberMap s p q b H) ≫
          (mappingPathStrictFiberToHomotopyFiber q b ≫
            TopCat.homotopyFiberPath q b) := by simp [Category.assoc]
      _ = (homotopyFiberToMappingPathStrictFiber p b ≫
            mappingPathStrictFiberMap s p q b H) ≫
          (pullback.fst (mappingPathProjection q)
            (TopCat.const (X := TopCat.of PUnit) b) ≫
              mappingPathPath q) := by
        rw [mappingPathStrictFiberToHomotopyFiber_path]
      _ = homotopyFiberToMappingPathStrictFiber p b ≫
          (mappingPathStrictFiberMap s p q b H ≫
            pullback.fst (mappingPathProjection q)
              (TopCat.const (X := TopCat.of PUnit) b)) ≫
                mappingPathPath q := by simp [Category.assoc]
      _ = homotopyFiberToMappingPathStrictFiber p b ≫
          (pullback.fst (mappingPathProjection p)
              (TopCat.const (X := TopCat.of PUnit) b) ≫
            mappingPathMapOfHomotopy s p q H) ≫
              mappingPathPath q := by
        rw [mappingPathStrictFiberMap_fst]
      _ = (homotopyFiberToMappingPathStrictFiber p b ≫
            pullback.fst (mappingPathProjection p)
              (TopCat.const (X := TopCat.of PUnit) b)) ≫
          mappingPathMapOfHomotopy s p q H ≫
            mappingPathPath q := by simp [Category.assoc]
      _ = (homotopyFiberToMappingPath p b ≫
            mappingPathMapOfHomotopy s p q H) ≫
              mappingPathPath q := by
        rw [homotopyFiberToMappingPathStrictFiber_fst]
        exact (Category.assoc _ _ _).symm
      _ = homotopyFiberToMappingPath p b ≫
            prependMappingPath s p q H := by
        rw [Category.assoc, mappingPathMapOfHomotopy_path]
      _ = prependHomotopyFiberPath s p q b H :=
        homotopyFiberToMappingPath_prepend s p q b H
      _ = homotopyFiberMapOfHomotopy s p q b H ≫
            TopCat.homotopyFiberPath q b := by
        exact (homotopyFiberMapOfHomotopy_path_map s p q b H).symm

private theorem homotopyFiberMapOfHomotopy_mem_weak_of_endpoint
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom)
    (hs : TopCat.weakHomotopyEquivalences s)
    (hEndpoint :
      let _ : ModelCategory TopCat.{u} := TopCat.modelCategory
      Fibration (TopCat.pathEndpoints B)) :
    TopCat.weakHomotopyEquivalences
      (homotopyFiberMapOfHomotopy s p q b H) := by
  have hstrict := mappingPathStrictFiberMap_mem_weakHomotopyEquivalences
    s p q b H hs hEndpoint
  have hinv : TopCat.weakHomotopyEquivalences
      (mappingPathStrictFiberIso p b).inv :=
    TopCat.weakHomotopyEquivalences.of_isIso _
  have hhom : TopCat.weakHomotopyEquivalences
      (mappingPathStrictFiberIso q b).hom :=
    TopCat.weakHomotopyEquivalences.of_isIso _
  have hcomp := TopCat.weakHomotopyEquivalences.comp_mem _ _
    (TopCat.weakHomotopyEquivalences.comp_mem _ _ hinv hstrict) hhom
  have heq :
      ((mappingPathStrictFiberIso p b).inv ≫
          mappingPathStrictFiberMap s p q b H) ≫
          (mappingPathStrictFiberIso q b).hom =
        homotopyFiberMapOfHomotopy s p q b H := by
    simpa [Category.assoc] using
      mappingPathStrictFiberIso_naturality s p q b H
  rw [heq] at hcomp
  exact hcomp

private theorem homotopyFiberMapOfHomotopy_mem_weakHomotopyEquivalences
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom)
    (hs : TopCat.weakHomotopyEquivalences s) :
    TopCat.weakHomotopyEquivalences
      (homotopyFiberMapOfHomotopy s p q b H) :=
  homotopyFiberMapOfHomotopy_mem_weak_of_endpoint s p q b H hs
    (TopCat.modelCategory.pathEndpoints_fibration_data B)

end

end TopCatHomotopySquarePreflight

namespace TopCat

open CategoryTheory Topology

/-- Transport between compact-open homotopy fibers along a specified homotopy
square. The total point is sent through the source map, and the supplied
homotopy path is prepended to the original fiber path. -/
noncomputable def homotopyFiberMapOfHomotopy
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    homotopyFiber p b ⟶ homotopyFiber q b :=
  TopCatHomotopySquarePreflight.homotopyFiberMapOfHomotopy s p q b H

@[reassoc (attr := simp)]
theorem homotopyFiberMapOfHomotopy_toTotal
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    homotopyFiberMapOfHomotopy s p q b H ≫ homotopyFiberToTotal q b =
      homotopyFiberToTotal p b ≫ s := by
  exact TopCatHomotopySquarePreflight.homotopyFiberMapOfHomotopy_toTotal
    s p q b H

@[simp]
theorem homotopyFiberMapOfHomotopy_path
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom)
    (z : homotopyFiber p b) (t : TopCat.I.{u}) :
    homotopyFiberPath q b (homotopyFiberMapOfHomotopy s p q b H z) t =
      if h : ((TopCat.I.homeomorph t : unitInterval) : ℝ) ≤ 1 / 2 then
        H (⟨2 * TopCat.I.homeomorph t,
          (unitInterval.mul_pos_mem_iff zero_lt_two).2
            ⟨(TopCat.I.homeomorph t).2.1, h⟩⟩,
          homotopyFiberToTotal p b z)
      else
        homotopyFiberPath p b z
          (TopCat.I.homeomorph.symm
            ⟨2 * TopCat.I.homeomorph t - 1,
              unitInterval.two_mul_sub_one_mem_iff.2
                ⟨(not_le.1 h).le, (TopCat.I.homeomorph t).2.2⟩⟩) := by
  rw [homotopyFiberMapOfHomotopy]
  rw [TopCatHomotopySquarePreflight.homotopyFiberMapOfHomotopy_path]
  rw [Path.trans_apply]
  rfl

/-- The canonical constant homotopy for the identity square of a map. -/
def homotopyFiberIdentitySquareHomotopy
    {X B : TopCat.{u}} (p : X ⟶ B) :
    ContinuousMap.Homotopy ((𝟙 X) ≫ p).hom p.hom :=
  TopCatHomotopySquarePreflight.identitySquareHomotopy p

/-- The canonical identity-square homotopy is constant on every original total point. -/
theorem homotopyFiberIdentitySquareHomotopy_apply
    {X B : TopCat.{u}} (p : X ⟶ B) (t : unitInterval) (x : X) :
    homotopyFiberIdentitySquareHomotopy p (t, x) = p x := by
  rfl

/-- The canonical constant homotopy associated to a strictly commuting square. -/
def homotopyFiberStrictSquareHomotopy
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (h : s ≫ q = p) :
    ContinuousMap.Homotopy (s ≫ q).hom p.hom :=
  TopCatHomotopySquarePreflight.strictSquareHomotopy s p q h

/-- The canonical composite of two homotopies defining composable squares. -/
def homotopyFiberCompositeSquareHomotopy
    {X Y Z B : TopCat.{u}}
    (s : X ⟶ Y) (t : Y ⟶ Z) (p : X ⟶ B) (q : Y ⟶ B)
    (r : Z ⟶ B)
    (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom)
    (K : ContinuousMap.Homotopy (t ≫ r).hom q.hom) :
    ContinuousMap.Homotopy ((s ≫ t) ≫ r).hom p.hom :=
  TopCatHomotopySquarePreflight.compositeSquareHomotopy s t p q r H K

/-- Transport along the identity square is homotopic to the identity. -/
noncomputable def homotopyFiberMapOfHomotopyIdHomotopy
    {X B : TopCat.{u}} (p : X ⟶ B) (b : B) :
    ContinuousMap.Homotopy
      (homotopyFiberMapOfHomotopy (𝟙 X) p p b
        (homotopyFiberIdentitySquareHomotopy p)).hom
      ((𝟙 (homotopyFiber p b) :
        homotopyFiber p b ⟶ homotopyFiber p b).hom) := by
  simpa [homotopyFiberMapOfHomotopy,
    homotopyFiberIdentitySquareHomotopy] using
      (TopCatHomotopySquarePreflight.identityCoherenceStatement_proof
        p b).some

/-- For a strictly commuting square, homotopy-square transport agrees up to
homotopy with the ordinary homotopy-pullback map. -/
noncomputable def homotopyFiberMapOfHomotopyStrictHomotopy
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (h : s ≫ q = p) :
    ContinuousMap.Homotopy
      (homotopyFiberMapOfHomotopy s p q b
        (homotopyFiberStrictSquareHomotopy s p q h)).hom
      (homotopyPullbackMap s (𝟙 (TopCat.of PUnit)) (𝟙 B)
        (by simp [h]) (by simp)).hom := by
  simpa [homotopyFiberMapOfHomotopy,
    homotopyFiberStrictSquareHomotopy] using
      (TopCatHomotopySquarePreflight.constantSquareCoherenceStatement_proof
        s p q b h).some

/-- Successive homotopy-square transports are homotopic to transport for the
canonical composite square homotopy. -/
noncomputable def homotopyFiberMapOfHomotopyCompHomotopy
    {X Y Z B : TopCat.{u}}
    (s : X ⟶ Y) (t : Y ⟶ Z) (p : X ⟶ B) (q : Y ⟶ B)
    (r : Z ⟶ B) (b : B)
    (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom)
    (K : ContinuousMap.Homotopy (t ≫ r).hom q.hom) :
    ContinuousMap.Homotopy
      (homotopyFiberMapOfHomotopy s p q b H ≫
        homotopyFiberMapOfHomotopy t q r b K).hom
      (homotopyFiberMapOfHomotopy (s ≫ t) p r b
        (homotopyFiberCompositeSquareHomotopy s t p q r H K)).hom := by
  simpa [homotopyFiberMapOfHomotopy,
    homotopyFiberCompositeSquareHomotopy] using
      (TopCatHomotopySquarePreflight.compositionCoherenceStatement_proof
        s t p q r b H K).some

theorem homotopyFiberMapOfHomotopy_mem_weakHomotopyEquivalences
    {X Y B : TopCat.{u}} (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (b : B) (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom)
    (hs : weakHomotopyEquivalences s) :
    weakHomotopyEquivalences (homotopyFiberMapOfHomotopy s p q b H) := by
  exact TopCatHomotopySquarePreflight.homotopyFiberMapOfHomotopy_mem_weakHomotopyEquivalences
    s p q b H hs

-- Compatibility alias retaining the previously published constructor name.
@[deprecated homotopyFiberMapOfHomotopyIdHomotopy (since := "2026-10-17"),
  nolint defsWithUnderscore]
alias homotopyFiberMapOfHomotopy_id_homotopy := homotopyFiberMapOfHomotopyIdHomotopy

-- Compatibility alias retaining the previously published constructor name.
@[deprecated homotopyFiberMapOfHomotopyStrictHomotopy (since := "2026-10-17"),
  nolint defsWithUnderscore]
alias homotopyFiberMapOfHomotopy_strict_homotopy := homotopyFiberMapOfHomotopyStrictHomotopy

-- Compatibility alias retaining the previously published constructor name.
@[deprecated homotopyFiberMapOfHomotopyCompHomotopy (since := "2026-10-17"),
  nolint defsWithUnderscore]
alias homotopyFiberMapOfHomotopy_comp_homotopy := homotopyFiberMapOfHomotopyCompHomotopy

end TopCat

end


public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Topology
open scoped unitInterval TopCat.modelCategory

universe u

/-!
## The original mapping-path replacement as public derived data

This record forwards the actual existing private mapping-path construction.
Its fibration proof uses the original jointly continuous endpoint lifts.
Its strict-fiber isomorphism retains the complete original source/path data.
-/

namespace TopCat

/-- The actual mapping-path fibration, both original total-space maps and
whole inverse families, and its exact compact-open strict-fiber comparison. -/
public structure MappingPathReplacementData {X B : TopCat.{u}} (p : X ⟶ B) where
  /-- The original mapping-path total space. -/
  space : TopCat.{u}
  /-- The original projection to the source point. -/
  toSource : space ⟶ X
  /-- The endpoint projection of the original carried path. -/
  toBase : space ⟶ B
  /-- The complete original carried path in the target. -/
  pathMap : space ⟶ pathObject B
  /-- The original section with its constant target path. -/
  inclusion : X ⟶ space
  inclusionToSource : inclusion ≫ toSource = 𝟙 X
  inclusionToBase : inclusion ≫ toBase = p
  inclusionPath : inclusion ≫ pathMap = p ≫ pathConstant B
  pathZero : pathMap ≫ pathEvalZero B = toSource ≫ p
  pathOne : pathMap ≫ pathEvalOne B = toBase
  /-- The original full contraction from section after source projection to the total identity. -/
  sourceHomotopy : ContinuousMap.Homotopy (toSource ≫ inclusion).hom
    (𝟙 space : space ⟶ space).hom
  /-- The original full homotopy from source projection after section to the source identity. -/
  sourceInverseHomotopy : ContinuousMap.Homotopy (inclusion ≫ toSource).hom
    (𝟙 X : X ⟶ X).hom
  projectionFibration : letI : ModelCategory TopCat.{u} := TopCat.modelCategory;
    Fibration toBase
  /-- The exact comparison of the endpoint fiber with the original compact-open homotopy fiber. -/
  strictFiberIso : (b : B) →
    pullback toBase (TopCat.const (X := TopCat.of PUnit) b) ≅ homotopyFiber p b
  strictFiberIsoTotal : ∀ b,
    (strictFiberIso b).hom ≫ homotopyFiberToTotal p b =
      pullback.fst toBase (TopCat.const b) ≫ toSource
  strictFiberIsoPath : ∀ b,
    (strictFiberIso b).hom ≫ homotopyFiberPath p b =
      pullback.fst toBase (TopCat.const b) ≫ pathMap
  strictFiberInvTotal : ∀ b,
    (strictFiberIso b).inv ≫ pullback.fst toBase (TopCat.const b) ≫ toSource =
      homotopyFiberToTotal p b
  strictFiberInvPath : ∀ b,
    (strictFiberIso b).inv ≫ pullback.fst toBase (TopCat.const b) ≫ pathMap =
      homotopyFiberPath p b

/-- Reuse the SAME original private mapping-path programs and the proved
unconditional endpoint fibration. No fibration or inverse outcome is supplied. -/
public def mappingPathReplacement {X B : TopCat.{u}} (p : X ⟶ B) :
    MappingPathReplacementData p :=
  { space := TopCatHomotopySquarePreflight.mappingPath p
    toSource := TopCatHomotopySquarePreflight.mappingPathToSource p
    toBase := TopCatHomotopySquarePreflight.mappingPathProjection p
    pathMap := TopCatHomotopySquarePreflight.mappingPathPath p
    inclusion := TopCatHomotopySquarePreflight.mappingPathSection p
    inclusionToSource := TopCatHomotopySquarePreflight.mappingPathSection_source p
    inclusionToBase := by
      change TopCatHomotopySquarePreflight.mappingPathSection p ≫
        (TopCatHomotopySquarePreflight.mappingPathPath p ≫ pathEvalOne B) = p
      rw [← Category.assoc, TopCatHomotopySquarePreflight.mappingPathSection_path,
        Category.assoc, pathConstant_evalOne, Category.comp_id]
    inclusionPath := TopCatHomotopySquarePreflight.mappingPathSection_path p
    pathZero := (pullback.condition :
      TopCatHomotopySquarePreflight.mappingPathToSource p ≫ p =
        TopCatHomotopySquarePreflight.mappingPathPath p ≫ pathEvalZero B).symm
    pathOne := rfl
    sourceHomotopy := TopCatHomotopySquarePreflight.mappingPathSourceHomotopy p
    sourceInverseHomotopy :=
      { toFun := fun z => z.2
        continuous_toFun := continuous_snd
        map_zero_left := fun x => (ConcreteCategory.congr_hom
          (TopCatHomotopySquarePreflight.mappingPathSection_source p) x).symm
        map_one_left := fun _ => rfl }
    projectionFibration :=
      TopCatHomotopySquarePreflight.mappingPathProjection_fibration_of_endpoint p
        (TopCat.modelCategory.pathEndpoints_fibration B)
    strictFiberIso := TopCatHomotopySquarePreflight.mappingPathStrictFiberIso p
    strictFiberIsoTotal := fun b =>
      TopCatHomotopySquarePreflight.mappingPathStrictFiberToHomotopyFiber_total p b
    strictFiberIsoPath := fun b =>
      TopCatHomotopySquarePreflight.mappingPathStrictFiberToHomotopyFiber_path p b
    strictFiberInvTotal := by
      intro b
      change TopCatHomotopySquarePreflight.homotopyFiberToMappingPathStrictFiber p b ≫
        pullback.fst (TopCatHomotopySquarePreflight.mappingPathProjection p)
          (TopCat.const b) ≫ TopCatHomotopySquarePreflight.mappingPathToSource p =
            homotopyFiberToTotal p b
      rw [← Category.assoc,
        TopCatHomotopySquarePreflight.homotopyFiberToMappingPathStrictFiber_fst,
        TopCatHomotopySquarePreflight.homotopyFiberToMappingPath_source]
    strictFiberInvPath := by
      intro b
      change TopCatHomotopySquarePreflight.homotopyFiberToMappingPathStrictFiber p b ≫
        pullback.fst (TopCatHomotopySquarePreflight.mappingPathProjection p)
          (TopCat.const b) ≫ TopCatHomotopySquarePreflight.mappingPathPath p =
            homotopyFiberPath p b
      rw [← Category.assoc,
        TopCatHomotopySquarePreflight.homotopyFiberToMappingPathStrictFiber_fst,
        TopCatHomotopySquarePreflight.homotopyFiberToMappingPath_path] }

private theorem mappingPathReplacementIsPullbackComputed
    {X B : TopCat.{u}} (p : X ⟶ B) :
    IsPullback (mappingPathReplacement p).toSource (mappingPathReplacement p).pathMap
      p (pathEvalZero B) := by
  change IsPullback (pullback.fst p (pathEvalZero B))
    (pullback.snd p (pathEvalZero B)) p (pathEvalZero B)
  exact IsPullback.of_hasPullback p (pathEvalZero B)

/-- The actual original source and whole path projections retain the
original mapping-path pullback universal property. -/
public theorem mappingPathReplacement_isPullback
    {X B : TopCat.{u}} (p : X ⟶ B) :
    IsPullback (mappingPathReplacement p).toSource (mappingPathReplacement p).pathMap
      p (pathEvalZero B) :=
  mappingPathReplacementIsPullbackComputed p

private theorem mappingPathReplacementExtComputed {X B : TopCat.{u}} (p : X ⟶ B)
    {z w : (mappingPathReplacement p).space}
    (hx : (mappingPathReplacement p).toSource z = (mappingPathReplacement p).toSource w)
    (hc : ∀ t : TopCat.I.{u},
      (mappingPathReplacement p).pathMap z t = (mappingPathReplacement p).pathMap w t) :
    z = w := by
  let Z : TopCat.{u} := TopCat.of PUnit.{u + 1}
  let f : Z ⟶ (mappingPathReplacement p).space := TopCat.const z
  let g : Z ⟶ (mappingPathReplacement p).space := TopCat.const w
  have hf : f ≫ (mappingPathReplacement p).toSource =
      g ≫ (mappingPathReplacement p).toSource := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro _
    exact hx
  have hg : f ≫ (mappingPathReplacement p).pathMap =
      g ≫ (mappingPathReplacement p).pathMap := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro _
    exact ContinuousMap.ext hc
  exact ConcreteCategory.congr_hom ((mappingPathReplacement_isPullback p).hom_ext hf hg)
    PUnit.unit

/-- Original mapping-path points are determined by their source and complete carried curve. -/
public theorem mappingPathReplacement_ext {X B : TopCat.{u}} (p : X ⟶ B)
    {z w : (mappingPathReplacement p).space}
    (hx : (mappingPathReplacement p).toSource z = (mappingPathReplacement p).toSource w)
    (hc : ∀ t : TopCat.I.{u},
      (mappingPathReplacement p).pathMap z t = (mappingPathReplacement p).pathMap w t) :
    z = w :=
  mappingPathReplacementExtComputed p hx hc

/-- The original carried path, with the standard interval parameter and actual endpoints. -/
public def mappingPathReplacementRootPath {X B : TopCat.{u}} (p : X ⟶ B)
    (z : (mappingPathReplacement p).space) :
    Path (p ((mappingPathReplacement p).toSource z)) ((mappingPathReplacement p).toBase z) :=
  TopCatHomotopySquarePreflight.mappingPathRootPath p z

private theorem mappingPathReplacementRootPathApplyComputed {X B : TopCat.{u}} (p : X ⟶ B)
    (z : (mappingPathReplacement p).space) (t : unitInterval) :
    mappingPathReplacementRootPath p z t =
      (mappingPathReplacement p).pathMap z (TopCat.I.homeomorph.symm t) := rfl

/-- Every original carried-path value is read through the actual interval homeomorphism. -/
public theorem mappingPathReplacementRootPath_apply {X B : TopCat.{u}} (p : X ⟶ B)
    (z : (mappingPathReplacement p).space) (t : unitInterval) :
    mappingPathReplacementRootPath p z t =
      (mappingPathReplacement p).pathMap z (TopCat.I.homeomorph.symm t) :=
  mappingPathReplacementRootPathApplyComputed p z t

/-- Reuse the already proved original mapping-path map for a square over the same base. -/
public def mappingPathReplacementMapOfHomotopy {X Y B : TopCat.{u}}
    (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    (mappingPathReplacement p).space ⟶ (mappingPathReplacement q).space :=
  TopCatHomotopySquarePreflight.mappingPathMapOfHomotopy s p q H

/-- The entire original mapping-path map retains its actual source component. -/
public theorem mappingPathReplacementMapOfHomotopy_toSource {X Y B : TopCat.{u}}
    (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    mappingPathReplacementMapOfHomotopy s p q H ≫ (mappingPathReplacement q).toSource =
      (mappingPathReplacement p).toSource ≫ s :=
  TopCatHomotopySquarePreflight.mappingPathMapOfHomotopy_source s p q H

/-- The entire original mapping-path map retains its actual endpoint projection. -/
public theorem mappingPathReplacementMapOfHomotopy_toBase {X Y B : TopCat.{u}}
    (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom) :
    mappingPathReplacementMapOfHomotopy s p q H ≫ (mappingPathReplacement q).toBase =
      (mappingPathReplacement p).toBase :=
  TopCatHomotopySquarePreflight.mappingPathMapOfHomotopy_projection s p q H

private theorem mappingPathReplacementMapOfHomotopyPathApplyComputed {X Y B : TopCat.{u}}
    (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom)
    (z : (mappingPathReplacement p).space) (t : TopCat.I.{u}) :
    (mappingPathReplacement q).pathMap (mappingPathReplacementMapOfHomotopy s p q H z) t =
      ((H.evalAt ((mappingPathReplacement p).toSource z)).trans
        (mappingPathReplacementRootPath p z)) (TopCat.I.homeomorph t) := by
  have h := ConcreteCategory.congr_hom
    (TopCatHomotopySquarePreflight.mappingPathMapOfHomotopy_path s p q H) z
  exact congrArg (fun gamma : pathObject B => gamma t) h

/-- The complete original carried path prepends the actual square path to the original path. -/
public theorem mappingPathReplacementMapOfHomotopy_path_apply {X Y B : TopCat.{u}}
    (s : X ⟶ Y) (p : X ⟶ B) (q : Y ⟶ B)
    (H : ContinuousMap.Homotopy (s ≫ q).hom p.hom)
    (z : (mappingPathReplacement p).space) (t : TopCat.I.{u}) :
    (mappingPathReplacement q).pathMap (mappingPathReplacementMapOfHomotopy s p q H z) t =
      ((H.evalAt ((mappingPathReplacement p).toSource z)).trans
        (mappingPathReplacementRootPath p z)) (TopCat.I.homeomorph t) :=
  mappingPathReplacementMapOfHomotopyPathApplyComputed s p q H z t

private theorem mappingPathReplacementSourceHomotopyToSourceComputed
    {X B : TopCat.{u}} (p : X ⟶ B) (t : unitInterval)
    (z : (mappingPathReplacement p).space) :
    (mappingPathReplacement p).toSource
        ((mappingPathReplacement p).sourceHomotopy.toContinuousMap.toFun (t, z)) =
      (mappingPathReplacement p).toSource z := by
  change TopCatHomotopySquarePreflight.mappingPathToSource p
      ((TopCatHomotopySquarePreflight.mappingPathSourceHomotopy p).toContinuousMap.toFun
        (t, z)) = TopCatHomotopySquarePreflight.mappingPathToSource p z
  have h : TopCatHomotopySquarePreflight.mappingPathContractionMap p ≫
      TopCatHomotopySquarePreflight.mappingPathToSource p =
    (TopCat.ofHom
      { toFun := fun w : unitInterval × TopCatHomotopySquarePreflight.mappingPath p => w.2
        continuous_toFun := continuous_snd }) ≫
      TopCatHomotopySquarePreflight.mappingPathToSource p := by
    change TopCatHomotopySquarePreflight.mappingPathContractionMap p ≫
        pullback.fst p (pathEvalZero B) =
      (TopCat.ofHom
        { toFun := fun w : unitInterval × TopCatHomotopySquarePreflight.mappingPath p => w.2
          continuous_toFun := continuous_snd }) ≫ pullback.fst p (pathEvalZero B)
    rw [TopCatHomotopySquarePreflight.mappingPathContractionMap, pullback.lift_fst]
  exact ConcreteCategory.congr_hom h (t, z)

/-- Every contraction time retains the complete original total coordinate. -/
public theorem mappingPathReplacement_sourceHomotopy_toSource
    {X B : TopCat.{u}} (p : X ⟶ B) (t : unitInterval)
    (z : (mappingPathReplacement p).space) :
    (mappingPathReplacement p).toSource
        ((mappingPathReplacement p).sourceHomotopy.toContinuousMap.toFun (t, z)) =
      (mappingPathReplacement p).toSource z :=
  mappingPathReplacementSourceHomotopyToSourceComputed p t z

private theorem mappingPathReplacementSourceHomotopyPathComputed
    {X B : TopCat.{u}} (p : X ⟶ B) (t : unitInterval)
    (z : (mappingPathReplacement p).space) (s : TopCat.I.{u}) :
    (mappingPathReplacement p).pathMap
        ((mappingPathReplacement p).sourceHomotopy.toContinuousMap.toFun (t, z)) s =
      (mappingPathReplacement p).pathMap z
        (TopCat.I.homeomorph.symm (t * TopCat.I.homeomorph s)) := by
  change TopCatHomotopySquarePreflight.mappingPathPath p
      ((TopCatHomotopySquarePreflight.mappingPathSourceHomotopy p).toContinuousMap.toFun
        (t, z)) s = TopCatHomotopySquarePreflight.mappingPathPath p z
          (TopCat.I.homeomorph.symm (t * TopCat.I.homeomorph s))
  have h : TopCatHomotopySquarePreflight.mappingPathContractionMap p ≫
      TopCatHomotopySquarePreflight.mappingPathPath p =
    TopCatHomotopySquarePreflight.mappingPathContractionPath p := by
    rw [TopCatHomotopySquarePreflight.mappingPathContractionMap,
      TopCatHomotopySquarePreflight.mappingPathPath, pullback.lift_snd]
  exact congrArg (fun gamma : pathObject B => gamma s)
    (ConcreteCategory.congr_hom h (t, z))

/-- The whole original carried path uses exactly the original product clock. -/
public theorem mappingPathReplacement_sourceHomotopy_path
    {X B : TopCat.{u}} (p : X ⟶ B) (t : unitInterval)
    (z : (mappingPathReplacement p).space) (s : TopCat.I.{u}) :
    (mappingPathReplacement p).pathMap
        ((mappingPathReplacement p).sourceHomotopy.toContinuousMap.toFun (t, z)) s =
      (mappingPathReplacement p).pathMap z
        (TopCat.I.homeomorph.symm (t * TopCat.I.homeomorph s)) :=
  mappingPathReplacementSourceHomotopyPathComputed p t z s

private theorem mappingPathReplacementSourceHomotopyProjectionComputed
    {X B : TopCat.{u}} (p : X ⟶ B) (t : unitInterval)
    (z : (mappingPathReplacement p).space) :
    (mappingPathReplacement p).toBase
        ((mappingPathReplacement p).sourceHomotopy.toContinuousMap.toFun (t, z)) =
      (mappingPathReplacement p).pathMap z (TopCat.I.homeomorph.symm t) := by
  change TopCatHomotopySquarePreflight.mappingPathPath p
      ((TopCatHomotopySquarePreflight.mappingPathSourceHomotopy p).toContinuousMap.toFun
        (t, z)) (1 : TopCat.I.{u}) = TopCatHomotopySquarePreflight.mappingPathPath p z
          ((TopCat.I.homeomorph.{u}).symm t)
  have h := mappingPathReplacementSourceHomotopyPathComputed p t z (1 : TopCat.I.{u})
  change TopCatHomotopySquarePreflight.mappingPathPath p
      ((TopCatHomotopySquarePreflight.mappingPathSourceHomotopy p).toContinuousMap.toFun
        (t, z)) (1 : TopCat.I.{u}) = TopCatHomotopySquarePreflight.mappingPathPath p z
          ((TopCat.I.homeomorph.{u}).symm
            (t * (TopCat.I.homeomorph.{u}) (1 : TopCat.I.{u}))) at h
  simpa only [TopCat.I.homeomorph_one.{u}, mul_one] using h

/-- The moving projection is the original path at the exact original time. -/
public theorem mappingPathReplacement_sourceHomotopy_projection
    {X B : TopCat.{u}} (p : X ⟶ B) (t : unitInterval)
    (z : (mappingPathReplacement p).space) :
    (mappingPathReplacement p).toBase
        ((mappingPathReplacement p).sourceHomotopy.toContinuousMap.toFun (t, z)) =
      (mappingPathReplacement p).pathMap z (TopCat.I.homeomorph.symm t) :=
  mappingPathReplacementSourceHomotopyProjectionComputed p t z

private theorem mappingPathReplacementSourceInverseHomotopyValueComputed
    {X B : TopCat.{u}} (p : X ⟶ B) (t : unitInterval) (x : X) :
    (mappingPathReplacement p).sourceInverseHomotopy.toContinuousMap.toFun (t, x) = x := rfl

/-- The other whole inverse family is the original strict identity return. -/
public theorem mappingPathReplacement_sourceInverseHomotopy_value
    {X B : TopCat.{u}} (p : X ⟶ B) (t : unitInterval) (x : X) :
    (mappingPathReplacement p).sourceInverseHomotopy.toContinuousMap.toFun (t, x) = x :=
  mappingPathReplacementSourceInverseHomotopyValueComputed p t x

end TopCat

end
