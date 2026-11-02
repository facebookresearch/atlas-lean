/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.Sets.VietorisTopology
import Mathlib.Topology.Baire.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory
open scoped MeasureTheory ENNReal

namespace MathlibExt.MeasureTheory.Geometry.BesicovitchKakeyaWanted

/-- Bowtie: union of slope-`u` segments through the pivot `(c, a)`,
for `u` ranging over `[u₁, u₂]`. -/
private def kakBowtie (c a u₁ u₂ : ℝ) : Set (ℝ × ℝ) :=
  (fun p : ℝ × ℝ => (c + p.1 * (p.2 - a), p.2)) '' (Set.Icc u₁ u₂ ×ˢ Set.Icc 0 1)

/-- Slope grid point: `-1 + 2k/N`. -/
private noncomputable def kakSlope (N k : ℕ) : ℝ := -1 + 2 * (k : ℝ) / (N : ℝ)

/-- Finite bowtie approximation: a finite set plus `N` consecutive bowties. -/
private def kakBowtieApprox (F : Set (ℝ × ℝ)) (N : ℕ) (x : ℕ → ℝ) (a : ℝ) :
    Set (ℝ × ℝ) :=
  F ∪ ⋃ k ∈ (Finset.range N : Set ℕ),
    kakBowtie (x k + kakSlope N k * a) a (kakSlope N k) (kakSlope N (k + 1))

/-- The Kakeya family: nonempty compact sets inside the strip `ℝ × [0,1]`
containing a slope-`u` segment for every `u ∈ [-1,1]`. -/
private def kakFamily : Set (TopologicalSpace.NonemptyCompacts (ℝ × ℝ)) :=
  {P | (P : Set (ℝ × ℝ)) ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧
    ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∃ x : ℝ,
      ∀ t ∈ Set.Icc (0 : ℝ) 1, (x + u * t, t) ∈ (P : Set (ℝ × ℝ))}

/-- Cavalieri-type area bound from uniform slice bounds. -/
private theorem kak_volume_le_of_slice_le {A : Set (ℝ × ℝ)} {a b : ℝ} {c : ℝ≥0∞}
    (hA : MeasurableSet A) (hsub : A ⊆ Set.univ ×ˢ Set.Icc a b)
    (hslice : ∀ s ∈ Set.Icc a b, volume {x : ℝ | (x, s) ∈ A} ≤ c) :
    volume A ≤ c * ENNReal.ofReal (b - a) := by
  have hvol : (volume : Measure (ℝ × ℝ)) A
      = ∫⁻ s, volume {x : ℝ | (x, s) ∈ A} ∂(volume : Measure ℝ) := by
    rw [MeasureTheory.Measure.volume_eq_prod,
      MeasureTheory.Measure.prod_apply_symm hA]
    apply MeasureTheory.lintegral_congr
    intro s
    rfl
  rw [hvol]
  calc ∫⁻ s, volume {x : ℝ | (x, s) ∈ A} ∂(volume : Measure ℝ)
      ≤ ∫⁻ s, (Set.Icc a b).indicator (fun _ => c) s ∂(volume : Measure ℝ) := by
        apply MeasureTheory.lintegral_mono
        intro s
        by_cases hs : s ∈ Set.Icc a b
        · rw [Set.indicator_of_mem hs]
          exact hslice s hs
        · rw [Set.indicator_of_notMem hs]
          have hempty : {x : ℝ | (x, s) ∈ A} = ∅ := by
            ext x
            simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
            intro hx
            exact hs (hsub hx).2
          dsimp only
          rw [hempty, MeasureTheory.measure_empty]
    _ = c * volume (Set.Icc a b) :=
        MeasureTheory.lintegral_indicator_const measurableSet_Icc c
    _ = c * ENNReal.ofReal (b - a) := by rw [Real.volume_Icc]

/-- A bowtie is compact. -/
private theorem kak_bowtie_isCompact (c a u₁ u₂ : ℝ) :
    IsCompact (kakBowtie c a u₁ u₂) := by
  unfold kakBowtie
  exact (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)

/-- A bowtie with `u₁ ≤ u₂` is nonempty. -/
private theorem kak_bowtie_nonempty (c a u₁ u₂ : ℝ) (h : u₁ ≤ u₂) :
    (kakBowtie c a u₁ u₂).Nonempty := by
  unfold kakBowtie
  apply Set.Nonempty.image
  exact ⟨(u₁, 0),
    ⟨Set.mem_Icc.mpr ⟨le_rfl, h⟩,
      Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩⟩⟩

/-- A bowtie lies in the strip. -/
private theorem kak_bowtie_subset_strip (c a u₁ u₂ : ℝ) :
    kakBowtie c a u₁ u₂ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 := by
  unfold kakBowtie
  rintro _ ⟨⟨_, t⟩, ⟨_, ht⟩, rfl⟩
  exact ⟨Set.mem_univ _, ht⟩

/-- A bowtie contains the slope-`u` segment with base `c - u * a`. -/
private theorem kak_bowtie_mem (c a u₁ u₂ u t : ℝ) (hu : u ∈ Set.Icc u₁ u₂)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (c - u * a + u * t, t) ∈ kakBowtie c a u₁ u₂ := by
  unfold kakBowtie
  refine ⟨(u, t), ⟨hu, ht⟩, ?_⟩
  change (c + u * (t - a), t) = (c - u * a + u * t, t)
  have h1 : c + u * (t - a) = c - u * a + u * t := by ring
  rw [h1]

/-- Points of a bowtie project near the left-edge segment. -/
private theorem kak_bowtie_dist (c a u₁ u₂ : ℝ) (p : ℝ × ℝ)
    (hp : p ∈ kakBowtie c a u₁ u₂) :
    p.2 ∈ Set.Icc (0 : ℝ) 1 ∧
      dist p (c + u₁ * (p.2 - a), p.2) ≤ (u₂ - u₁) * (1 + |a|) := by
  unfold kakBowtie at hp
  obtain ⟨⟨u, t⟩, ⟨hu, ht⟩, hpt⟩ := hp
  have huI : u₁ ≤ u ∧ u ≤ u₂ := hu
  have htI : (0 : ℝ) ≤ t ∧ t ≤ 1 := ht
  have hpt' : (c + u * (t - a), t) = p := hpt
  have hpt2 : t = p.2 := by rw [← hpt']
  have htIcc : p.2 ∈ Set.Icc (0 : ℝ) 1 := hpt2 ▸ ht
  refine ⟨htIcc, ?_⟩
  have hnonneg : (0 : ℝ) ≤ (u₂ - u₁) * (1 + |a|) :=
    mul_nonneg (sub_nonneg.mpr (le_trans huI.1 huI.2))
      (add_nonneg zero_le_one (abs_nonneg _))
  have h1 : |(c + u * (t - a)) - (c + u₁ * (t - a))| ≤ (u₂ - u₁) * (1 + |a|) := by
    have hsub : (c + u * (t - a)) - (c + u₁ * (t - a)) = (u - u₁) * (t - a) := by
      ring
    rw [hsub, abs_mul]
    have huu : |u - u₁| ≤ u₂ - u₁ := by
      rw [abs_of_nonneg (sub_nonneg.mpr huI.1)]
      linarith [huI.2]
    have hta : |t - a| ≤ 1 + |a| := by
      have ht1 : |t| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [htI.1, htI.2]
      calc |t - a| ≤ |t| + |a| := abs_sub _ _
        _ ≤ 1 + |a| := by linarith
    exact mul_le_mul huu hta (abs_nonneg _)
      (sub_nonneg.mpr (le_trans huI.1 huI.2))
  rw [← hpt', Prod.dist_eq]
  dsimp only
  rw [Real.dist_eq, dist_self]
  exact max_le h1 hnonneg

/-- A bowtie slice is contained in the unordered interval between its edges. -/
private theorem kak_bowtie_slice_volume_le (c a u₁ u₂ s : ℝ) (hle : u₁ ≤ u₂) :
    volume {x : ℝ | (x, s) ∈ kakBowtie c a u₁ u₂}
      ≤ ENNReal.ofReal ((u₂ - u₁) * |s - a|) := by
  have hsub : {x : ℝ | (x, s) ∈ kakBowtie c a u₁ u₂}
      ⊆ Set.uIcc (c + u₁ * (s - a)) (c + u₂ * (s - a)) := by
    intro x hx
    unfold kakBowtie at hx
    obtain ⟨⟨u, t⟩, ⟨hu, ht⟩, hxt⟩ := hx
    have huI : u₁ ≤ u ∧ u ≤ u₂ := hu
    have htI : (0 : ℝ) ≤ t ∧ t ≤ 1 := ht
    have hxt' : (c + u * (t - a), t) = (x, s) := hxt
    have ht1 : t = s := (Prod.ext_iff.mp hxt').2
    have hx1 : c + u * (t - a) = x := (Prod.ext_iff.mp hxt').1
    rw [Set.mem_uIcc]
    by_cases hsa : 0 ≤ s - a
    · left
      have e1 : c + u₁ * (s - a) ≤ x := by
        rw [← hx1, ht1]
        have : u₁ * (s - a) ≤ u * (s - a) :=
          mul_le_mul_of_nonneg_right huI.1 hsa
        linarith
      have e2 : x ≤ c + u₂ * (s - a) := by
        rw [← hx1, ht1]
        have : u * (s - a) ≤ u₂ * (s - a) :=
          mul_le_mul_of_nonneg_right huI.2 hsa
        linarith
      exact ⟨e1, e2⟩
    · right
      have hsa : s - a < 0 := lt_of_not_ge hsa
      have e1 : c + u₂ * (s - a) ≤ x := by
        rw [← hx1, ht1]
        have : u₂ * (s - a) ≤ u * (s - a) :=
          mul_le_mul_of_nonpos_right huI.2 hsa.le
        linarith
      have e2 : x ≤ c + u₁ * (s - a) := by
        rw [← hx1, ht1]
        have : u * (s - a) ≤ u₁ * (s - a) :=
          mul_le_mul_of_nonpos_right huI.1 hsa.le
        linarith
      exact ⟨e1, e2⟩
  calc volume {x : ℝ | (x, s) ∈ kakBowtie c a u₁ u₂}
      ≤ volume (Set.uIcc (c + u₁ * (s - a)) (c + u₂ * (s - a))) :=
        measure_mono hsub
    _ = ENNReal.ofReal ((u₂ - u₁) * |s - a|) := by
        rw [Real.volume_interval]
        congr 1
        have hring : (c + u₂ * (s - a)) - (c + u₁ * (s - a))
            = (u₂ - u₁) * (s - a) := by ring
        rw [hring, abs_mul, abs_of_nonneg (sub_nonneg.mpr hle)]

/-- Grid points lie in `[-1, 1]`. -/
private theorem kak_slope_mem {N : ℕ} (hN : 1 ≤ N) {k : ℕ} (hk : k ≤ N) :
    kakSlope N k ∈ Set.Icc (-1 : ℝ) 1 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hkN : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  unfold kakSlope
  rw [Set.mem_Icc]
  constructor
  · have hnn : (0 : ℝ) ≤ 2 * (k : ℝ) / (N : ℝ) :=
      div_nonneg (by positivity) (Nat.cast_nonneg _)
    linarith
  · have h2 : 2 * (k : ℝ) / (N : ℝ) ≤ 2 := by
      rw [div_le_iff₀ hNpos]
      nlinarith
    linarith

/-- Consecutive grid points differ by `2/N`. -/
private theorem kak_slope_step {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    kakSlope N (k + 1) - kakSlope N k = 2 / (N : ℝ) := by
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  unfold kakSlope
  push_cast
  field_simp
  ring

/-- Every `u ∈ [-1,1]` sits between consecutive grid points. -/
private theorem kak_slope_cover {N : ℕ} (hN : 1 ≤ N) {u : ℝ}
    (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ k : ℕ, k < N ∧ kakSlope N k ≤ u ∧ u ≤ kakSlope N (k + 1) := by
  rw [Set.mem_Icc] at hu
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  set r : ℝ := (u + 1) * (N : ℝ) / 2 with hr
  have hr0 : 0 ≤ r := by
    rw [hr]
    exact div_nonneg (mul_nonneg (by linarith [hu.1]) (Nat.cast_nonneg _))
      (by norm_num)
  have hfloor : (⌊r⌋₊ : ℝ) ≤ r := Nat.floor_le hr0
  have hceil : r < (⌊r⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one r
  by_cases hj : ⌊r⌋₊ < N
  · refine ⟨⌊r⌋₊, hj, ?_, ?_⟩
    · unfold kakSlope
      have h1 : 2 * (⌊r⌋₊ : ℝ) / (N : ℝ) ≤ u + 1 := by
        rw [div_le_iff₀ hNpos]
        have : (⌊r⌋₊ : ℝ) * 2 ≤ (u + 1) * (N : ℝ) := by
          have hrw : r * 2 = (u + 1) * (N : ℝ) := by rw [hr]; ring
          nlinarith [hfloor]
        nlinarith
      linarith
    · unfold kakSlope
      have h1 : u + 1 ≤ 2 * ((⌊r⌋₊ : ℝ) + 1) / (N : ℝ) := by
        rw [le_div_iff₀ hNpos]
        have hrw : r * 2 = (u + 1) * (N : ℝ) := by rw [hr]; ring
        have : (u + 1) * (N : ℝ) ≤ ((⌊r⌋₊ : ℝ) + 1) * 2 := by nlinarith [hceil]
        nlinarith
      have hcast : ((⌊r⌋₊ + 1 : ℕ) : ℝ) = (⌊r⌋₊ : ℝ) + 1 := by
        rw [Nat.cast_add, Nat.cast_one]
      rw [hcast] at *
      linarith
  · have hj' : N ≤ ⌊r⌋₊ := le_of_not_gt hj
    refine ⟨N - 1, Nat.sub_lt (by omega : 0 < N) (by norm_num), ?_, ?_⟩
    · have hNM : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ N)]
        norm_num
      unfold kakSlope
      rw [hNM]
      have h1 : 2 * ((N : ℝ) - 1) / (N : ℝ) ≤ u + 1 := by
        rw [div_le_iff₀ hNpos]
        have hNr : (N : ℝ) ≤ r := le_trans (by exact_mod_cast hj') hfloor
        have hrw : r * 2 = (u + 1) * (N : ℝ) := by rw [hr]; ring
        nlinarith [hNr]
      linarith
    · have hkk : N - 1 + 1 = N := Nat.sub_add_cancel hN
      rw [hkk]
      unfold kakSlope
      have h2N : 2 * (N : ℝ) / (N : ℝ) = 2 := by rw [div_eq_iff hNne]
      have hgoal : (-1 : ℝ) + 2 * (N : ℝ) / (N : ℝ) = 1 := by
        linear_combination h2N
      rw [hgoal]
      exact hu.2

/-- Hausdorff limits contain limits of points. -/
private theorem kak_mem_of_tendsto {α : Type*} [MetricSpace α]
    {Q : ℕ → TopologicalSpace.NonemptyCompacts α} {P : TopologicalSpace.NonemptyCompacts α}
    (hQ : Filter.Tendsto Q Filter.atTop (nhds P))
    {y : ℕ → α} (hy : ∀ n, y n ∈ (Q n : Set α)) {z : α}
    (hz : Filter.Tendsto y Filter.atTop (nhds z)) :
    z ∈ (P : Set α) := by
  have hPne := P.nonempty
  have hfin : ∀ n, Metric.hausdorffEDist (Q n : Set α) (P : Set α) ≠ ⊤ := fun n =>
    Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded (Q n).nonempty hPne
      (Q n).isCompact.isBounded P.isCompact.isBounded
  have hH : Filter.Tendsto (fun n => Metric.hausdorffDist (Q n : Set α) (P : Set α))
      Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun n => dist (Q n) P) Filter.atTop (nhds 0) :=
      tendsto_iff_dist_tendsto_zero.mp hQ
    simpa [TopologicalSpace.NonemptyCompacts.dist_eq] using h0
  have hD : Filter.Tendsto (fun n => dist z (y n)) Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun n => dist (y n) z) Filter.atTop (nhds 0) :=
      tendsto_iff_dist_tendsto_zero.mp hz
    simpa [dist_comm] using h0
  have hbound : ∀ n, Metric.infDist z (P : Set α)
      ≤ dist z (y n) + Metric.hausdorffDist (Q n : Set α) (P : Set α) := by
    intro n
    calc Metric.infDist z (P : Set α)
        ≤ Metric.infDist z (Q n : Set α)
            + Metric.hausdorffDist (Q n : Set α) (P : Set α) :=
          Metric.infDist_le_infDist_add_hausdorffDist (hfin n)
      _ ≤ dist z (y n) + Metric.hausdorffDist (Q n : Set α) (P : Set α) :=
          add_le_add_left (Metric.infDist_le_dist_of_mem (hy n)) _
  have hsum : Filter.Tendsto
      (fun n => dist z (y n) + Metric.hausdorffDist (Q n : Set α) (P : Set α))
      Filter.atTop (nhds (0 + 0)) := hD.add hH
  rw [add_zero] at hsum
  have hle : Metric.infDist z (P : Set α) ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hsum hbound
  have h0 : Metric.infDist z (P : Set α) = 0 :=
    le_antisymm hle Metric.infDist_nonneg
  have hmem : z ∈ closure (P : Set α) :=
    (Metric.mem_closure_iff_infDist_zero hPne).mpr h0
  rwa [P.isCompact.isClosed.closure_eq] at hmem

/-- Volume of the intersection is upper semicontinuous in `P`. -/
private theorem kak_isOpen_volume_inter_lt (C : Set (ℝ × ℝ)) (c : ℝ≥0∞) :
    IsOpen {P : TopologicalSpace.NonemptyCompacts (ℝ × ℝ) |
      volume ((P : Set (ℝ × ℝ)) ∩ C) < c} := by
  rw [Metric.isOpen_iff]
  intro P hP
  have hPmeas : MeasurableSet (P : Set (ℝ × ℝ)) := P.isCompact.measurableSet
  have hct : ∀ r : ℝ, MeasurableSet (Metric.cthickening r (P : Set (ℝ × ℝ))) :=
    fun r => Metric.isClosed_cthickening.measurableSet
  have htend : Filter.Tendsto
      (fun r => volume (Metric.cthickening r (P : Set (ℝ × ℝ)) ∩ C))
      (nhds 0) (nhds (volume ((P : Set (ℝ × ℝ)) ∩ C))) := by
    have h := tendsto_measure_cthickening_of_isCompact
      (μ := volume.restrict C) P.isCompact
    simpa [MeasureTheory.Measure.restrict_apply (hct _),
      MeasureTheory.Measure.restrict_apply hPmeas] using h
  have hev : ∀ᶠ _x in nhds (0 : ℝ),
      volume (Metric.cthickening _x (P : Set (ℝ × ℝ)) ∩ C) < c :=
    Filter.Tendsto.eventually_lt_const hP htend
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hεpos, hε⟩ := hev
  refine ⟨ε / 2, by positivity, fun Q hQ => ?_⟩
  have hrlt : volume (Metric.cthickening (ε / 2) (P : Set (ℝ × ℝ)) ∩ C) < c := by
    apply hε
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε / 2)]
    exact half_lt_self hεpos
  have hQP : (Q : Set (ℝ × ℝ)) ⊆ Metric.cthickening (ε / 2) (P : Set (ℝ × ℝ)) := by
    intro q hq
    have hfin : Metric.hausdorffEDist (Q : Set (ℝ × ℝ)) (P : Set (ℝ × ℝ)) ≠ ⊤ :=
      Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded Q.nonempty P.nonempty
        Q.isCompact.isBounded P.isCompact.isBounded
    have hH : Metric.hausdorffDist (Q : Set (ℝ × ℝ)) (P : Set (ℝ × ℝ)) < ε / 2 := by
      have hdist : dist Q P < ε / 2 := hQ
      rwa [TopologicalSpace.NonemptyCompacts.dist_eq] at hdist
    have hinf : Metric.infDist q (P : Set (ℝ × ℝ)) < ε / 2 :=
      lt_of_le_of_lt (Metric.infDist_le_hausdorffDist_of_mem hq hfin) hH
    have hmem : q ∈ Metric.thickening (ε / 2) (P : Set (ℝ × ℝ)) :=
      (Metric.mem_thickening_iff_infDist_lt P.nonempty).mpr hinf
    exact Metric.thickening_subset_cthickening _ _ hmem
  calc volume ((Q : Set (ℝ × ℝ)) ∩ C)
      ≤ volume (Metric.cthickening (ε / 2) (P : Set (ℝ × ℝ)) ∩ C) :=
        measure_mono (Set.inter_subset_inter hQP (fun x hx => hx))
    _ < c := hrlt

/-- The Kakeya family is closed. -/
private theorem kak_isClosed_kakeyaFamily : IsClosed kakFamily := by
  apply isClosed_of_closure_subset
  intro P hP
  have hPstrip : (P : Set (ℝ × ℝ)) ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 := by
    have hclosed : IsClosed {Q : TopologicalSpace.NonemptyCompacts (ℝ × ℝ) |
        (Q : Set (ℝ × ℝ)) ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1} :=
      TopologicalSpace.NonemptyCompacts.isClosed_subsets_of_isClosed
        (isClosed_univ.prod isClosed_Icc)
    exact closure_minimal (fun Q hQ => hQ.1) hclosed hP
  refine ⟨hPstrip, fun u hu => ?_⟩
  have hQ : ∀ n : ℕ, ∃ Qn : TopologicalSpace.NonemptyCompacts (ℝ × ℝ),
      Qn ∈ kakFamily ∧ dist Qn P < 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨Qn, hQnmem, hQndist⟩ := Metric.mem_closure_iff.mp hP _ hpos
    refine ⟨Qn, hQnmem, ?_⟩
    rw [dist_comm]
    exact hQndist
  choose Q hQmem hQdist using hQ
  have hx : ∀ n : ℕ, ∃ xn : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (xn + u * t, t) ∈ (Q n : Set (ℝ × ℝ)) := fun n => (hQmem n).2 u hu
  choose x hxseg using hx
  have hx0 : ∀ n : ℕ, (x n, 0) ∈ (Q n : Set (ℝ × ℝ)) := by
    intro n
    have h := hxseg n 0 (Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩)
    simpa using h
  have hfin : ∀ n, Metric.hausdorffEDist (Q n : Set (ℝ × ℝ)) (P : Set (ℝ × ℝ)) ≠ ⊤ :=
    fun n => Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded (Q n).nonempty
      P.nonempty (Q n).isCompact.isBounded P.isCompact.isBounded
  have hH : ∀ n, Metric.hausdorffDist (Q n : Set (ℝ × ℝ)) (P : Set (ℝ × ℝ)) < 1 := by
    intro n
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith
    calc Metric.hausdorffDist (Q n : Set (ℝ × ℝ)) (P : Set (ℝ × ℝ))
        = dist (Q n) P := TopologicalSpace.NonemptyCompacts.dist_eq.symm
      _ < 1 / ((n : ℝ) + 1) := hQdist n
      _ ≤ 1 := h1
  have hpt : ∀ n : ℕ, (x n, 0) ∈ Metric.cthickening 1 (P : Set (ℝ × ℝ)) := by
    intro n
    have hinf : Metric.infDist (x n, 0) (P : Set (ℝ × ℝ)) < 1 :=
      lt_of_le_of_lt (Metric.infDist_le_hausdorffDist_of_mem (hx0 n) (hfin n)) (hH n)
    have hmem : (x n, 0) ∈ Metric.thickening 1 (P : Set (ℝ × ℝ)) :=
      (Metric.mem_thickening_iff_infDist_lt P.nonempty).mpr hinf
    exact Metric.thickening_subset_cthickening 1 _ hmem
  obtain ⟨z, _, φ, hφmono, hφlim⟩ := (P.isCompact.cthickening).tendsto_subseq hpt
  have hQlim : Filter.Tendsto (fun k => Q (φ k)) Filter.atTop (nhds P) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hcomp : Filter.Tendsto (fun k => 1 / ((((φ k : ℕ)) : ℝ) + 1))
        Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφmono.tendsto_atTop
    refine squeeze_zero (fun k => dist_nonneg) (fun k => le_of_lt (hQdist (φ k))) hcomp
  have hfst : Filter.Tendsto (fun k => x (φ k)) Filter.atTop (nhds z.1) :=
    (continuous_fst.tendsto z).comp hφlim
  refine ⟨z.1, fun t ht => ?_⟩
  refine kak_mem_of_tendsto (Q := fun k => Q (φ k)) hQlim
    (y := fun k => (x (φ k) + u * t, t)) ?_ ?_
  · intro k
    exact hxseg (φ k) t ht
  · exact (hfst.add tendsto_const_nhds).prodMk_nhds tendsto_const_nhds

/-- The Kakeya family is nonempty (filled triangle). -/
private theorem kak_kakeyaFamily_nonempty :
    ∃ P : TopologicalSpace.NonemptyCompacts (ℝ × ℝ), P ∈ kakFamily := by
  refine ⟨⟨⟨kakBowtie 0 0 (-1) 1, kak_bowtie_isCompact 0 0 (-1) 1⟩,
    kak_bowtie_nonempty 0 0 (-1) 1 (by norm_num)⟩, ?_, ?_⟩
  · exact kak_bowtie_subset_strip 0 0 (-1) 1
  · intro u hu
    refine ⟨0, fun t ht => ?_⟩
    change (0 + u * t, t) ∈ kakBowtie 0 0 (-1) 1
    simpa using kak_bowtie_mem 0 0 (-1) 1 u t hu ht

/-- Bowtie approximations are compact. -/
private theorem kak_bowtieApprox_isCompact (F : Set (ℝ × ℝ)) (hF : F.Finite)
    (N : ℕ) (x : ℕ → ℝ) (a : ℝ) : IsCompact (kakBowtieApprox F N x a) := by
  unfold kakBowtieApprox
  apply IsCompact.union hF.isCompact
  apply Set.Finite.isCompact_biUnion (Finset.finite_toSet _)
  intro k _
  exact kak_bowtie_isCompact _ _ _ _

/-- Bowtie approximations are nonempty. -/
private theorem kak_bowtieApprox_nonempty (F : Set (ℝ × ℝ)) {N : ℕ} (hN : 1 ≤ N)
    (x : ℕ → ℝ) (a : ℝ) : (kakBowtieApprox F N x a).Nonempty := by
  have hle : kakSlope N 0 ≤ kakSlope N (0 + 1) := by
    have h := kak_slope_step hN 0
    have hnn : (0 : ℝ) ≤ 2 / (N : ℝ) :=
      div_nonneg zero_le_two (Nat.cast_nonneg _)
    linarith
  have h0 : (kakBowtie (x 0 + kakSlope N 0 * a) a (kakSlope N 0)
      (kakSlope N (0 + 1))).Nonempty :=
    kak_bowtie_nonempty _ _ _ _ hle
  have hmem : (0 : ℕ) ∈ (Finset.range N : Set ℕ) :=
    Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega))
  have hsub : kakBowtie (x 0 + kakSlope N 0 * a) a (kakSlope N 0)
      (kakSlope N (0 + 1)) ⊆ kakBowtieApprox F N x a := by
    unfold kakBowtieApprox
    intro p hp
    right
    exact Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨hmem, hp⟩⟩
  obtain ⟨p, hp⟩ := h0
  exact ⟨p, hsub hp⟩

/-- Bowtie approximations of strip sets lie in the strip. -/
private theorem kak_bowtieApprox_subset_strip (F : Set (ℝ × ℝ)) (N : ℕ)
    (x : ℕ → ℝ) (a : ℝ)
    (hF : F ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1) :
    kakBowtieApprox F N x a ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 := by
  unfold kakBowtieApprox
  intro p hp
  rcases hp with hpF | hpU
  · exact hF hpF
  · simp only [Set.mem_iUnion] at hpU
    obtain ⟨k, _, hkp⟩ := hpU
    exact kak_bowtie_subset_strip _ _ _ _ hkp

/-- Bowtie approximations contain a segment in every direction. -/
private theorem kak_bowtieApprox_slope (F : Set (ℝ × ℝ)) {N : ℕ} (hN : 1 ≤ N)
    (x : ℕ → ℝ) (a : ℝ) {u : ℝ} (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ x' : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (x' + u * t, t) ∈ kakBowtieApprox F N x a := by
  obtain ⟨k, hkN, hk1, hk2⟩ := kak_slope_cover hN hu
  refine ⟨x k + (kakSlope N k - u) * a, fun t ht => ?_⟩
  have hmem : (x k + kakSlope N k * a - u * a + u * t, t) ∈
      kakBowtie (x k + kakSlope N k * a) a (kakSlope N k) (kakSlope N (k + 1)) :=
    kak_bowtie_mem _ _ _ _ _ _ (Set.mem_Icc.mpr ⟨hk1, hk2⟩) ht
  have heq : x k + (kakSlope N k - u) * a + u * t
      = x k + kakSlope N k * a - u * a + u * t := by ring
  rw [heq]
  unfold kakBowtieApprox
  right
  exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr
    ⟨Finset.mem_coe.mpr (Finset.mem_range.mpr hkN), hmem⟩⟩

/-- The Hausdorff distance from `P` to a bowtie approximation. -/
private theorem kak_dist_bowtieApprox_le
    (P : TopologicalSpace.NonemptyCompacts (ℝ × ℝ))
    {F : Set (ℝ × ℝ)} {N : ℕ} {x : ℕ → ℝ} {a ρ : ℝ}
    (hρ : 0 ≤ ρ) (hFsub : F ⊆ (P : Set (ℝ × ℝ)))
    (hFcov : ∀ p ∈ (P : Set (ℝ × ℝ)), ∃ q ∈ F, dist p q ≤ ρ)
    (hN : 1 ≤ N) (hρN : 2 / (N : ℝ) * (1 + |a|) ≤ ρ)
    (hx : ∀ k : ℕ, k < N → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (x k + kakSlope N k * t, t) ∈ (P : Set (ℝ × ℝ))) :
    Metric.hausdorffDist (P : Set (ℝ × ℝ)) (kakBowtieApprox F N x a) ≤ ρ := by
  apply Metric.hausdorffDist_le_of_mem_dist hρ
  · intro p hp
    obtain ⟨q, hqF, hqp⟩ := hFcov p hp
    refine ⟨q, ?_, hqp⟩
    unfold kakBowtieApprox
    left
    exact hqF
  · intro q hq
    unfold kakBowtieApprox at hq
    rcases hq with hqF | hqU
    · refine ⟨q, hFsub hqF, ?_⟩
      rw [dist_self]
      exact hρ
    · simp only [Set.mem_iUnion] at hqU
      obtain ⟨k, hkmem, hkp⟩ := hqU
      have hkN : k < N := Finset.mem_range.mp (Finset.mem_coe.mp hkmem)
      have ht2 := (kak_bowtie_dist _ _ _ _ _ hkp).1
      refine ⟨(x k + kakSlope N k * q.2, q.2), hx k hkN q.2 ht2, ?_⟩
      have h0 := (kak_bowtie_dist _ _ _ _ _ hkp).2
      have hstep := kak_slope_step hN k
      have heq : (x k + kakSlope N k * a) + kakSlope N k * (q.2 - a)
          = x k + kakSlope N k * q.2 := by ring
      rw [heq, hstep] at h0
      exact le_trans h0 hρN

/-- Bowtie approximations meet slabs in small area. -/
private theorem kak_volume_bowtieApprox_inter_slab_le (F : Set (ℝ × ℝ))
    (hF : F.Finite) {N : ℕ} (hN : 1 ≤ N) (x : ℕ → ℝ) {a b : ℝ} (hab : a ≤ b) :
    volume (kakBowtieApprox F N x a ∩ (Set.univ ×ˢ Set.Icc a b))
      ≤ ENNReal.ofReal (2 * (b - a)) * ENNReal.ofReal (b - a) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hba : (0 : ℝ) ≤ b - a := sub_nonneg.mpr hab
  have hcomp : IsCompact (kakBowtieApprox F N x a) :=
    kak_bowtieApprox_isCompact F hF N x a
  have hAmeas : MeasurableSet
      (kakBowtieApprox F N x a ∩ (Set.univ ×ˢ Set.Icc a b)) :=
    hcomp.measurableSet.inter
      (MeasurableSet.prod MeasurableSet.univ measurableSet_Icc)
  refine kak_volume_le_of_slice_le hAmeas Set.inter_subset_right fun s hs => ?_
  rw [Set.mem_Icc] at hs
  have hsa : |s - a| ≤ b - a := by
    rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
    linarith [hs.2]
  have hslice_sub : {y : ℝ | (y, s) ∈ kakBowtieApprox F N x a ∩
        (Set.univ ×ˢ Set.Icc a b)}
      ⊆ {y : ℝ | (y, s) ∈ F} ∪ ⋃ k ∈ Finset.range N,
        {y : ℝ | (y, s) ∈ kakBowtie (x k + kakSlope N k * a) a
          (kakSlope N k) (kakSlope N (k + 1))} := by
    intro y hy
    have hyQ : (y, s) ∈ kakBowtieApprox F N x a := hy.1
    unfold kakBowtieApprox at hyQ
    rcases hyQ with hyF | hyU
    · left
      exact hyF
    · right
      simp only [Set.mem_iUnion] at hyU
      obtain ⟨k, hkmem, hkp⟩ := hyU
      have hkfin : k ∈ Finset.range N := Finset.mem_coe.mp hkmem
      exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hkfin, hkp⟩⟩
  have hF0 : volume {y : ℝ | (y, s) ∈ F} = 0 := by
    have hsub : {y : ℝ | (y, s) ∈ F} ⊆ Prod.fst '' F := by
      intro y hy
      exact ⟨(y, s), hy, rfl⟩
    have hfin : (Prod.fst '' F).Finite := hF.image _
    exact le_antisymm
      (le_trans (measure_mono hsub) (le_of_eq (hfin.measure_zero _))) zero_le
  have hterm : ∀ k : ℕ, k ∈ Finset.range N → volume
        {y : ℝ | (y, s) ∈ kakBowtie (x k + kakSlope N k * a) a
          (kakSlope N k) (kakSlope N (k + 1))}
        ≤ ENNReal.ofReal ((2 / (N : ℝ)) * (b - a)) := by
    intro k _
    have hkk : kakSlope N k ≤ kakSlope N (k + 1) := by
      have h := kak_slope_step hN k
      have hnn : (0 : ℝ) ≤ 2 / (N : ℝ) :=
        div_nonneg zero_le_two (Nat.cast_nonneg _)
      linarith
    calc volume {y : ℝ | (y, s) ∈ kakBowtie (x k + kakSlope N k * a) a
          (kakSlope N k) (kakSlope N (k + 1))}
        ≤ ENNReal.ofReal ((kakSlope N (k + 1) - kakSlope N k) * |s - a|) :=
          kak_bowtie_slice_volume_le _ _ _ _ _ hkk
      _ ≤ ENNReal.ofReal ((2 / (N : ℝ)) * (b - a)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [kak_slope_step hN k]
          exact mul_le_mul_of_nonneg_left hsa
            (div_nonneg zero_le_two (Nat.cast_nonneg _))
  have hsum : ∑ _k ∈ Finset.range N, ENNReal.ofReal ((2 / (N : ℝ)) * (b - a))
      = ENNReal.ofReal (2 * (b - a)) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ =>
      mul_nonneg (div_nonneg zero_le_two (Nat.cast_nonneg _)) hba)]
    congr 1
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have key : (2 : ℝ) / (N : ℝ) * (N : ℝ) = 2 := div_mul_cancel₀ _ hNne
    linear_combination (b - a) * key
  calc volume {y : ℝ | (y, s) ∈ kakBowtieApprox F N x a ∩
        (Set.univ ×ˢ Set.Icc a b)}
      ≤ volume {y : ℝ | (y, s) ∈ F} + volume (⋃ k ∈ Finset.range N,
        {y : ℝ | (y, s) ∈ kakBowtie (x k + kakSlope N k * a) a
          (kakSlope N k) (kakSlope N (k + 1))}) :=
        le_trans (measure_mono hslice_sub) (measure_union_le _ _)
    _ = volume (⋃ k ∈ Finset.range N, {y : ℝ | (y, s) ∈
        kakBowtie (x k + kakSlope N k * a) a
          (kakSlope N k) (kakSlope N (k + 1))}) := by rw [hF0, zero_add]
    _ ≤ ∑ k ∈ Finset.range N, volume {y : ℝ | (y, s) ∈
        kakBowtie (x k + kakSlope N k * a) a
          (kakSlope N k) (kakSlope N (k + 1))} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.range N, ENNReal.ofReal ((2 / (N : ℝ)) * (b - a)) :=
        Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (2 * (b - a)) := hsum

/-- Density of small-slab-volume approximants. -/
private theorem kak_exists_near_small_slab
    (P : TopologicalSpace.NonemptyCompacts (ℝ × ℝ)) (hP : P ∈ kakFamily)
    {a b : ℝ} (hab : a ≤ b) {r : ℝ} (hr : 0 < r) :
    ∃ Q : TopologicalSpace.NonemptyCompacts (ℝ × ℝ), Q ∈ kakFamily ∧
      dist Q P < r ∧ volume ((Q : Set (ℝ × ℝ)) ∩ (Set.univ ×ˢ Set.Icc a b))
        ≤ ENNReal.ofReal (2 * (b - a)) * ENNReal.ofReal (b - a) := by
  obtain ⟨F, hFsub, hFfin, hFcov⟩ := P.isCompact.finite_cover_balls (half_pos hr)
  obtain ⟨N, hNgt⟩ := exists_nat_gt (4 * (1 + |a|) / r)
  have hN1 : 1 ≤ N := by
    have hnn : (0 : ℝ) ≤ 4 * (1 + |a|) / r := by positivity
    have hpos : (0 : ℝ) < (N : ℝ) := lt_of_le_of_lt hnn hNgt
    have h0 : 0 < N := by exact_mod_cast hpos
    omega
  have hρ : 2 / (N : ℝ) * (1 + |a|) < r / 2 := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have h1 : 4 * (1 + |a|) < r * (N : ℝ) := by
      have h2 := (div_lt_iff₀ hr).mp hNgt
      nlinarith [h2]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hNpos]
    nlinarith [h1]
  have hxex : ∀ k : ℕ, ∃ xk : ℝ, (k < N → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (xk + kakSlope N k * t, t) ∈ (P : Set (ℝ × ℝ))) := by
    intro k
    by_cases hk : k < N
    · obtain ⟨xk, hxk⟩ := hP.2 (kakSlope N k)
        (kak_slope_mem hN1 (Nat.le_of_lt hk))
      exact ⟨xk, fun _ => hxk⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose x hx using hxex
  have hQset : IsCompact (kakBowtieApprox F N x a) :=
    kak_bowtieApprox_isCompact F hFfin N x a
  have hQne : (kakBowtieApprox F N x a).Nonempty :=
    kak_bowtieApprox_nonempty F hN1 x a
  set Q : TopologicalSpace.NonemptyCompacts (ℝ × ℝ) := ⟨⟨kakBowtieApprox F N x a,
    hQset⟩, hQne⟩
  have hQmem : Q ∈ kakFamily := by
    refine ⟨?_, fun u hu => ?_⟩
    · exact kak_bowtieApprox_subset_strip F N x a (fun q hq => hP.1 (hFsub hq))
    · obtain ⟨x', hx'⟩ := kak_bowtieApprox_slope F hN1 x a hu
      exact ⟨x', fun t ht => hx' t ht⟩
  refine ⟨Q, hQmem, ?_, ?_⟩
  · have hFcov' : ∀ p ∈ (P : Set (ℝ × ℝ)), ∃ q ∈ F, dist p q ≤ r / 2 := by
      intro p hp
      have hmem0 : p ∈ ⋃ x ∈ F, Metric.ball x (r / 2) := hFcov hp
      simp only [Set.mem_iUnion] at hmem0
      obtain ⟨q, hqF, hqp⟩ := hmem0
      refine ⟨q, hqF, ?_⟩
      rw [Metric.mem_ball] at hqp
      exact le_of_lt hqp
    have hle : Metric.hausdorffDist (P : Set (ℝ × ℝ))
        (kakBowtieApprox F N x a) ≤ r / 2 :=
      kak_dist_bowtieApprox_le P (half_pos hr).le hFsub hFcov' hN1 hρ.le
        (fun k hk t ht => hx k hk t ht)
    have heq : dist Q P
        = Metric.hausdorffDist (kakBowtieApprox F N x a) (P : Set (ℝ × ℝ)) :=
      TopologicalSpace.NonemptyCompacts.dist_eq
    rw [heq, Metric.hausdorffDist_comm]
    exact lt_of_le_of_lt hle (half_lt_self hr)
  · have heq : (Q : Set (ℝ × ℝ)) = kakBowtieApprox F N x a := rfl
    rw [heq]
    exact kak_volume_bowtieApprox_inter_slab_le F hFfin hN1 x hab

/-- The strip is covered by `M + 1` slabs. -/
private theorem kak_volume_le_sum_slabs (A : Set (ℝ × ℝ))
    (hA : A ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1) (M : ℕ) :
    volume A ≤ ∑ i ∈ Finset.range (M + 1),
      volume (A ∩ (Set.univ ×ˢ Set.Icc ((i : ℝ) / ((M : ℝ) + 1))
        (((i : ℝ) + 1) / ((M : ℝ) + 1)))) := by
  have hMpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hsub : A ⊆ ⋃ i ∈ Finset.range (M + 1),
      A ∩ (Set.univ ×ˢ Set.Icc ((i : ℝ) / ((M : ℝ) + 1))
        (((i : ℝ) + 1) / ((M : ℝ) + 1))) := by
    intro p hp
    have ht := (hA hp).2
    rw [Set.mem_Icc] at ht
    set j : ℕ := ⌊p.2 * ((M : ℝ) + 1)⌋₊ with hj
    have hj0 : 0 ≤ p.2 * ((M : ℝ) + 1) := mul_nonneg ht.1 hMpos.le
    have hfloor : (j : ℝ) ≤ p.2 * ((M : ℝ) + 1) := Nat.floor_le hj0
    have hceil : p.2 * ((M : ℝ) + 1) < (j : ℝ) + 1 := Nat.lt_floor_add_one _
    refine Set.mem_iUnion.mpr ⟨min j M, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_range.mpr
        (lt_of_le_of_lt (Nat.min_le_right j M) (Nat.lt_succ_self M))
    · refine ⟨hp, Set.mem_univ p.1, ?_⟩
      rw [Set.mem_Icc]
      constructor
      · rw [div_le_iff₀ hMpos]
        have hmin : ((min j M : ℕ) : ℝ) ≤ (j : ℝ) := by
          exact_mod_cast min_le_left j M
        exact le_trans hmin hfloor
      · rw [le_div_iff₀ hMpos]
        by_cases hjm : j ≤ M
        · have him : min j M = j := min_eq_left hjm
          rw [him]
          exact le_of_lt hceil
        · have hlt : M < j := lt_of_not_ge hjm
          have him : min j M = M := min_eq_right (le_of_lt hlt)
          rw [him]
          have hle := mul_le_mul_of_nonneg_right ht.2 hMpos.le
          linarith
  calc volume A
      ≤ volume (⋃ i ∈ Finset.range (M + 1), A ∩ (Set.univ ×ˢ Set.Icc
        ((i : ℝ) / ((M : ℝ) + 1)) (((i : ℝ) + 1) / ((M : ℝ) + 1)))) :=
        measure_mono hsub
    _ ≤ ∑ i ∈ Finset.range (M + 1), volume (A ∩ (Set.univ ×ˢ Set.Icc
        ((i : ℝ) / ((M : ℝ) + 1)) (((i : ℝ) + 1) / ((M : ℝ) + 1)))) :=
        measure_biUnion_finset_le _ _

/-- Baire gives a null set in the Kakeya family. -/
private theorem kak_exists_null_mem_kakeyaFamily :
    ∃ P : TopologicalSpace.NonemptyCompacts (ℝ × ℝ), P ∈ kakFamily ∧
      volume (P : Set (ℝ × ℝ)) = 0 := by
  have _complete := kak_isClosed_kakeyaFamily.completeSpace_coe
  obtain ⟨P₀, hP₀⟩ := kak_kakeyaFamily_nonempty
  have _hne : Nonempty ↥kakFamily := ⟨⟨P₀, hP₀⟩⟩
  set Y : Type := ↥kakFamily
  set slab : ℕ → ℕ → Set (ℝ × ℝ) := fun M i =>
    Set.univ ×ˢ Set.Icc ((i : ℝ) / ((M : ℝ) + 1)) (((i : ℝ) + 1) / ((M : ℝ) + 1))
  set G : ℕ → ℕ → Set Y := fun M i => Subtype.val ⁻¹'
    {Q : TopologicalSpace.NonemptyCompacts (ℝ × ℝ) |
      volume ((Q : Set (ℝ × ℝ)) ∩ slab M i) < ENNReal.ofReal (3 / (((M : ℝ) + 1) ^ 2))}
  have hslab : ∀ M i : ℕ, slab M i = Set.univ ×ˢ Set.Icc ((i : ℝ) / ((M : ℝ) + 1))
      (((i : ℝ) + 1) / ((M : ℝ) + 1)) := fun M i => rfl
  have hGmem : ∀ (M i : ℕ) (Q : Y), Q ∈ G M i ↔
      volume (((Q.val : TopologicalSpace.NonemptyCompacts (ℝ × ℝ)) :
        Set (ℝ × ℝ)) ∩ slab M i) <
        ENNReal.ofReal (3 / (((M : ℝ) + 1) ^ 2)) := fun M i Q => Iff.rfl
  have hMpos : ∀ M : ℕ, (0 : ℝ) < (M : ℝ) + 1 := fun M => by positivity
  have hGopen : ∀ M i : ℕ, IsOpen (G M i) := by
    intro M i
    exact IsOpen.preimage continuous_subtype_val
      (kak_isOpen_volume_inter_lt _ _)
  have hGdense : ∀ M i : ℕ, Dense (G M i) := by
    intro M i
    rw [Metric.dense_iff]
    intro P r hr
    have hab : (i : ℝ) / ((M : ℝ) + 1) ≤ ((i : ℝ) + 1) / ((M : ℝ) + 1) := by
      have h := mul_le_mul_of_nonneg_right (show (i : ℝ) ≤ (i : ℝ) + 1 by linarith)
        (inv_nonneg.mpr (hMpos M).le)
      simpa [div_eq_mul_inv] using h
    obtain ⟨Q, hQmem, hQdist, hQvol⟩ :=
      kak_exists_near_small_slab (↑P) P.property hab hr
    have hMne : ((M : ℝ) + 1) ≠ 0 := ne_of_gt (hMpos M)
    have hba : ((i : ℝ) + 1) / ((M : ℝ) + 1) - (i : ℝ) / ((M : ℝ) + 1)
        = 1 / ((M : ℝ) + 1) := by
      rw [← sub_div, show ((i : ℝ) + 1) - (i : ℝ) = 1 by ring]
    have hlt : ENNReal.ofReal (2 * (1 / ((M : ℝ) + 1))) *
        ENNReal.ofReal (1 / ((M : ℝ) + 1))
        < ENNReal.ofReal (3 / (((M : ℝ) + 1) ^ 2)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
      field_simp
      nlinarith [mul_lt_mul_of_pos_right (show (2 : ℝ) < 3 by norm_num)
        (show (0 : ℝ) < ((M : ℝ) + 1) ^ 2 by positivity)]
    refine ⟨⟨Q, hQmem⟩, ?_, ?_⟩
    · rw [Metric.mem_ball]
      exact hQdist
    · rw [hGmem]
      rw [hba] at hQvol
      exact lt_of_le_of_lt hQvol hlt
  have hdense : Dense (⋂ p : ℕ × ℕ, G p.1 p.2) := by
    apply dense_iInter_of_isOpen
    · intro p
      exact hGopen p.1 p.2
    · intro p
      exact hGdense p.1 p.2
  obtain ⟨P, hP⟩ := hdense.nonempty
  have hP' : ∀ M i : ℕ, P ∈ G M i := fun M i => Set.mem_iInter.mp hP (M, i)
  refine ⟨↑P, P.property, ?_⟩
  have hbound : ∀ M : ℕ, volume ((↑P : TopologicalSpace.NonemptyCompacts (ℝ × ℝ)) :
      Set (ℝ × ℝ)) ≤ ENNReal.ofReal (3 / ((M : ℝ) + 1)) := by
    intro M
    have hPM : ∀ i : ℕ, volume (((↑P : TopologicalSpace.NonemptyCompacts (ℝ × ℝ)) :
        Set (ℝ × ℝ)) ∩ slab M i) ≤ ENNReal.ofReal (3 / (((M : ℝ) + 1) ^ 2)) := by
      intro i
      have hi : P ∈ G M i := hP' M i
      have hmem : (↑P : TopologicalSpace.NonemptyCompacts (ℝ × ℝ)) ∈
          {Q : TopologicalSpace.NonemptyCompacts (ℝ × ℝ) |
            volume ((Q : Set (ℝ × ℝ)) ∩ slab M i) <
              ENNReal.ofReal (3 / (((M : ℝ) + 1) ^ 2))} := hi
      exact le_of_lt hmem
    have hsum' : ∑ i ∈ Finset.range (M + 1),
        volume (((↑P : TopologicalSpace.NonemptyCompacts (ℝ × ℝ)) : Set (ℝ × ℝ)) ∩
          slab M i) ≤ ENNReal.ofReal (3 / ((M : ℝ) + 1)) := by
      have hle : ∑ i ∈ Finset.range (M + 1),
          volume (((↑P : TopologicalSpace.NonemptyCompacts (ℝ × ℝ)) : Set (ℝ × ℝ)) ∩
            slab M i)
          ≤ ∑ _i ∈ Finset.range (M + 1),
            ENNReal.ofReal (3 / (((M : ℝ) + 1) ^ 2)) :=
        Finset.sum_le_sum (fun i _ => hPM i)
      have heq : ∑ _i ∈ Finset.range (M + 1),
          ENNReal.ofReal (3 / (((M : ℝ) + 1) ^ 2))
          = ENNReal.ofReal (3 / ((M : ℝ) + 1)) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
          div_nonneg (by norm_num) (by positivity))]
        congr 1
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          Nat.cast_add, Nat.cast_one]
        have hMne : ((M : ℝ) + 1) ≠ 0 := ne_of_gt (hMpos M)
        field_simp
      exact le_trans hle (le_of_eq heq)
    have hsum : ∑ i ∈ Finset.range (M + 1),
        volume (((↑P : TopologicalSpace.NonemptyCompacts (ℝ × ℝ)) : Set (ℝ × ℝ)) ∩
          (Set.univ ×ˢ Set.Icc ((i : ℝ) / ((M : ℝ) + 1))
            (((i : ℝ) + 1) / ((M : ℝ) + 1)))) ≤ ENNReal.ofReal (3 / ((M : ℝ) + 1)) :=
      hsum'
    have hcov := kak_volume_le_sum_slabs _ P.property.1 M
    exact le_trans hcov hsum
  have hlim : Filter.Tendsto (fun M : ℕ => ENNReal.ofReal (3 / ((M : ℝ) + 1)))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun M : ℕ => (3 : ℝ) * (1 / ((M : ℝ) + 1)))
        Filter.atTop (nhds (3 * 0)) :=
      Filter.Tendsto.const_mul 3 tendsto_one_div_add_atTop_nhds_zero_nat
    rw [mul_zero] at h1
    have h2 : (fun M : ℕ => ENNReal.ofReal (3 / ((M : ℝ) + 1)))
        = fun M : ℕ => ENNReal.ofReal ((3 : ℝ) * (1 / ((M : ℝ) + 1))) := by
      funext M
      congr 1
      ring
    rw [h2]
    simpa using ENNReal.tendsto_ofReal h1
  have hle : volume ((↑P : TopologicalSpace.NonemptyCompacts (ℝ × ℝ)) :
      Set (ℝ × ℝ)) ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hbound
  exact le_antisymm hle zero_le

/-- Slope segments give segments in all directions. -/
private theorem kak_exists_segment_of_slopes (P : Set (ℝ × ℝ))
    (hP : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∃ x : ℝ,
      ∀ t ∈ Set.Icc (0 : ℝ) 1, (x + u * t, t) ∈ P) :
    ∀ p q : ℝ, p ^ 2 + q ^ 2 = 1 →
      ∃ b : ℝ × ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        (b.1 + t * p, b.2 + t * q) ∈ P ∪ Prod.swap ⁻¹' P := by
  have hcase : ∀ p q : ℝ, p ^ 2 + q ^ 2 = 1 → |p| ≤ |q| →
      ∃ b : ℝ × ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, (b.1 + t * p, b.2 + t * q) ∈ P := by
    intro p q hpq hle
    have hq0 : q ≠ 0 := by
      rintro rfl
      have hp0 : p = 0 := abs_eq_zero.mp
        (le_antisymm (by simpa using hle) (abs_nonneg _))
      simp [hp0] at hpq
    have hp1 : |p| ≤ 1 := by
      have h1 : p ^ 2 ≤ 1 := by nlinarith [sq_nonneg q, hpq]
      rw [abs_le]
      constructor <;> nlinarith [h1, sq_nonneg (p - 1), sq_nonneg (p + 1)]
    have hq1 : |q| ≤ 1 := by
      have h1 : q ^ 2 ≤ 1 := by nlinarith [sq_nonneg p, hpq]
      rw [abs_le]
      constructor <;> nlinarith [h1, sq_nonneg (q - 1), sq_nonneg (q + 1)]
    have habs : |p / q| ≤ 1 := by
      rw [abs_div, div_le_one (abs_pos.mpr hq0)]
      exact hle
    have huI : p / q ∈ Set.Icc (-1 : ℝ) 1 := Set.mem_Icc.mpr (abs_le.mp habs)
    obtain ⟨x, hx⟩ := hP (p / q) huI
    have hts : ∀ t : ℝ, t * p = (p / q) * (t * q) := by
      intro t
      rw [div_mul_eq_mul_div, eq_div_iff hq0]
      ring
    by_cases hqpos : 0 < q
    · refine ⟨(x, 0), fun t ht => ?_⟩
      rw [Set.mem_Icc] at ht
      have hs : t * q ∈ Set.Icc (0 : ℝ) 1 := by
        rw [Set.mem_Icc]
        constructor
        · exact mul_nonneg ht.1 hqpos.le
        · have hqle : q ≤ 1 := (abs_le.mp hq1).2
          calc t * q ≤ 1 * q :=
                mul_le_mul_of_nonneg_right ht.2 hqpos.le
            _ = q := one_mul q
            _ ≤ 1 := hqle
      have hmem := hx (t * q) hs
      dsimp only
      rw [zero_add, hts t]
      exact hmem
    · have hqneg : q < 0 := by
        rcases lt_or_gt_of_ne hq0 with h | h
        · exact h
        · exact absurd h hqpos
      refine ⟨(x + (p / q) * (-q), -q), fun t ht => ?_⟩
      rw [Set.mem_Icc] at ht
      set s : ℝ := -q + t * q with hs
      have hsI : s ∈ Set.Icc (0 : ℝ) 1 := by
        have h1 : s = -q * (1 - t) := by rw [hs]; ring
        have hq1' : -q ≤ 1 := by
          have h := (abs_le.mp hq1).1
          linarith
        rw [Set.mem_Icc, h1]
        constructor
        · exact mul_nonneg (by linarith [hqneg]) (by linarith [ht.2])
        · calc -q * (1 - t) ≤ 1 * (1 - t) :=
              mul_le_mul_of_nonneg_right hq1' (by linarith [ht.2])
            _ = 1 - t := one_mul _
            _ ≤ 1 := by linarith [ht.1]
      have hmem := hx s hsI
      have heq1 : x + (p / q) * (-q) + t * p = x + (p / q) * s := by
        rw [hs]
        linear_combination hts t
      dsimp only
      rw [heq1]
      exact hmem
  intro p q hpq
  by_cases hle : |p| ≤ |q|
  · obtain ⟨b, hb⟩ := hcase p q hpq hle
    refine ⟨b, fun t ht => ?_⟩
    exact Set.mem_union_left _ (hb t ht)
  · have hlt : |q| < |p| := lt_of_not_ge hle
    have hpq' : q ^ 2 + p ^ 2 = 1 := by rw [add_comm]; exact hpq
    obtain ⟨b, hb⟩ := hcase q p hpq' hlt.le
    refine ⟨(b.2, b.1), fun t ht => ?_⟩
    have hmem := hb t ht
    have hmem2 : (b.2 + t * p, b.1 + t * q) ∈ Prod.swap ⁻¹' P := hmem
    dsimp only
    exact Set.mem_union_right _ hmem2

/-- Transfer to `EuclideanSpace ℝ (Fin 2)`. -/
private theorem kak_exists_kakeya_euclidean :
    ∃ K : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet K ∧ IsCompact K ∧
      volume K = 0 ∧ ∀ v : EuclideanSpace ℝ (Fin 2), ‖v‖ = 1 →
        ∃ a : EuclideanSpace ℝ (Fin 2), ∀ t ∈ Set.Icc (0 : ℝ) 1, a + t • v ∈ K := by
  obtain ⟨P, hPmem, hPvol⟩ := kak_exists_null_mem_kakeyaFamily
  set E : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (ℝ × ℝ) :=
    (EuclideanSpace.equiv (Fin 2) ℝ).trans
      (ContinuousLinearEquiv.finTwoArrow ℝ ℝ) with hEdef
  set K'' : Set (ℝ × ℝ) :=
    (P : Set (ℝ × ℝ)) ∪ Prod.swap ⁻¹' (P : Set (ℝ × ℝ)) with hKdef
  have hK''comp : IsCompact K'' := IsCompact.union P.isCompact
    ((Homeomorph.prodComm ℝ ℝ).isCompact_preimage.mpr P.isCompact)
  have hswap : MeasurePreserving Prod.swap (volume : Measure (ℝ × ℝ)) volume :=
    MeasureTheory.Measure.measurePreserving_swap
  have hK''vol : volume K'' = 0 := by
    have h2 : volume (Prod.swap ⁻¹' (P : Set (ℝ × ℝ))) = 0 := by
      have h := hswap.measure_preimage P.isCompact.nullMeasurableSet
      rw [hPvol] at h
      exact h
    have hle : volume K'' ≤ 0 := by
      calc volume K'' ≤ volume (P : Set (ℝ × ℝ)) +
            volume (Prod.swap ⁻¹' (P : Set (ℝ × ℝ))) := measure_union_le _ _
        _ = 0 := by rw [hPvol, h2, add_zero]
    exact le_antisymm hle zero_le
  have hMP : MeasurePreserving (⇑E) volume volume :=
    (MeasureTheory.volume_preserving_finTwoArrow ℝ).comp
      (PiLp.volume_preserving_ofLp (Fin 2))
  set K : Set (EuclideanSpace ℝ (Fin 2)) := ⇑E ⁻¹' K'' with hKdef2
  have hKeq : K = ⇑E ⁻¹' K'' := rfl
  have hKcomp : IsCompact K := by
    rw [hKeq]
    exact (E.toHomeomorph.isCompact_preimage).mpr hK''comp
  have hKvol : volume K = 0 := by
    have h := hMP.measure_preimage hK''comp.nullMeasurableSet
    rw [hK''vol] at h
    rw [hKeq]
    exact h
  refine ⟨K, hKcomp.measurableSet, hKcomp, hKvol, fun v hv => ?_⟩
  have hpq : (E v).1 ^ 2 + (E v).2 ^ 2 = 1 := by
    have he1 : (E v).1 = v.ofLp 0 := rfl
    have he2 : (E v).2 = v.ofLp 1 := rfl
    have hnorm : ‖v‖ ^ 2 = (v.ofLp 0) ^ 2 + (v.ofLp 1) ^ 2 := by
      have h := EuclideanSpace.norm_sq_eq v
      rw [Fin.sum_univ_two] at h
      rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs] at h
      exact h
    rw [he1, he2, ← hnorm, hv, one_pow]
  obtain ⟨b, hb⟩ := kak_exists_segment_of_slopes _ hPmem.2 (E v).1 (E v).2 hpq
  refine ⟨E.symm b, fun t ht => ?_⟩
  have hmem := hb t ht
  have himg : E (E.symm b + t • v) = (b.1 + t * (E v).1, b.2 + t * (E v).2) := by
    have hlin : E (E.symm b + t • v) = b + t • (E v) := by
      rw [E.map_add, E.map_smul, E.apply_symm_apply]
    have g1 : (b + t • E v).1 = b.1 + t * (E v).1 := by
      have r1 : (b + t • E v).1 = b.1 + (t • E v).1 := rfl
      have r2 : (t • E v).1 = t • (E v).1 := rfl
      rw [r1, r2, smul_eq_mul]
    have g2 : (b + t • E v).2 = b.2 + t * (E v).2 := by
      have r1 : (b + t • E v).2 = b.2 + (t • E v).2 := rfl
      have r2 : (t • E v).2 = t • (E v).2 := rfl
      rw [r1, r2, smul_eq_mul]
    rw [hlin, Prod.ext_iff]
    exact ⟨g1, g2⟩
  have e1 : E (E.symm b + t • v) ∈ K'' := by
    rw [himg]
    exact hmem
  rw [hKeq]
  exact e1

end MathlibExt.MeasureTheory.Geometry.BesicovitchKakeyaWanted

@[expose] public section

open MeasureTheory
open scoped MeasureTheory

namespace MathlibExt.MeasureTheory.Geometry.BesicovitchKakeyaWanted

/-!
# Besicovitch–Kakeya set in the plane

Records existence of a compact Lebesgue-null set in `ℝ²` containing a unit segment in every
direction.
-/

/--
**Besicovitch's Kakeya set of measure zero.** There is a compact set $K \subseteq \mathbb{R}^2$
of Lebesgue measure zero that contains a unit segment in every direction: $K$ is measurable,
and for every unit vector $v \in \mathbb{R}^2$ there is a point $a \in \mathbb{R}^2$ with
$a + t v \in K$ for all $t \in [0, 1]$.

The proof here follows T. W. Körner, "Besicovitch via Baire", Studia Math. 158 (2003): a
Baire-category argument in the Hausdorff metric space of compact sets, not a Perron-tree
construction.

Proves `Wanted` entry `besicovitch_kakeya_compact_measure_zero`.

Source: A. S. Besicovitch, Math. Z. 27
(1928) 312–320 and S. Kakeya, Tohoku Rep. 6 (1917); Perron-tree gives compact measure-zero Kakeya
set; Lean states compact Lebesgue-null oriented version in ℝ² with segments `a+t•v`, `t∈[0, 1]`.
-/
public theorem besicovitch_kakeya_compact_measure_zero
    [MeasurableSpace (EuclideanSpace ℝ (Fin 2))]
    [BorelSpace (EuclideanSpace ℝ (Fin 2))] :
    ∃ (K : Set (EuclideanSpace ℝ (Fin 2))),
      MeasurableSet K ∧ IsCompact K ∧
        ((volume : Measure (EuclideanSpace ℝ (Fin 2))) K = 0) ∧
        ∀ (v : EuclideanSpace ℝ (Fin 2)), ‖v‖ = 1 →
          ∃ (a : EuclideanSpace ℝ (Fin 2)), ∀ t ∈ Set.Icc (0 : ℝ) 1, a + t • v ∈ K := by
  have hloc : ‹MeasurableSpace (EuclideanSpace ℝ (Fin 2))›
      = WithLp.measurableSpace 2 (Fin 2 → ℝ) := by
    have e1 : ‹MeasurableSpace (EuclideanSpace ℝ (Fin 2))›
        = borel (EuclideanSpace ℝ (Fin 2)) :=
      BorelSpace.measurable_eq
    have e2 : WithLp.measurableSpace 2 (Fin 2 → ℝ)
        = borel (EuclideanSpace ℝ (Fin 2)) :=
      BorelSpace.measurable_eq
    exact e1.trans e2.symm
  subst hloc
  exact kak_exists_kakeya_euclidean

end MathlibExt.MeasureTheory.Geometry.BesicovitchKakeyaWanted
