/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.RegularVariationKaramata
public import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Truncated second moment of a regularly varying tail, corrected constant

For a probability measure `μ` on `ℝ` whose combined tail is regularly varying
of index `-α` with `0 < α < 2`, the truncated second moment satisfies

  `(∫ y in Icc (-x) x, y ^ 2 ∂μ) / (x ^ 2 * combinedTail μ x) → α / (2 - α)`.

## Source and statement correction

`v1/Atlas/TheoryOfProbability/code/RegularVariation.lean` states this with the
constant `2 / (2 - α)`, which is wrong: for the Pareto tail `P(|X| > x) = x ^ (-α)`
the ratio equals `α / (2 - α)` (see the test file, where the ratio is computed
directly). The proof here is the corrected statement, via Karamata's integral
theorem (`karamata_integral`) applied to the upper tail
`tailGe μ s = (μ {y | s ≤ |y|}).toReal` and a layer-cake computation.

## Main results

* `truncatedMoment_tendsto`: the corrected truncated-moment asymptotic.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace MathlibExt.Probability.TruncatedMoment

open MathlibExt.Probability.RegularVariation

/-- The upper tail `(μ {y | s ≤ |y|}).toReal`. -/
noncomputable def tailGe (μ : Measure ℝ) (s : ℝ) : ℝ := (μ {y : ℝ | s ≤ |y|}).toReal

/-- The lower tail `(μ {y | s < |y|}).toReal`. -/
noncomputable def tailGt (μ : Measure ℝ) (s : ℝ) : ℝ := (μ {y : ℝ | s < |y|}).toReal

theorem tailGe_nonneg (μ : Measure ℝ) (s : ℝ) : 0 ≤ tailGe μ s := ENNReal.toReal_nonneg

theorem tailGt_nonneg (μ : Measure ℝ) (s : ℝ) : 0 ≤ tailGt μ s := ENNReal.toReal_nonneg

theorem tailGe_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : ℝ) :
    tailGe μ s ≤ 1 := by
  unfold tailGe
  have h : μ {y : ℝ | s ≤ |y|} ≤ 1 := by
    calc μ {y : ℝ | s ≤ |y|} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).mpr h

theorem antitone_tailGe (μ : Measure ℝ) [IsFiniteMeasure μ] : Antitone (tailGe μ) := by
  intro a b hab
  unfold tailGe
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro y hy
  exact le_trans hab hy

theorem antitone_tailGt (μ : Measure ℝ) [IsFiniteMeasure μ] : Antitone (tailGt μ) := by
  intro a b hab
  unfold tailGt
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro y hy
  exact lt_of_le_of_lt hab hy

/-- At nonnegative thresholds the strict absolute tail is the canonical combined tail. -/
theorem tailGt_eq_combinedTail (μ : Measure ℝ) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0 ≤ s) : tailGt μ s = combinedTail μ s := by
  have hset : {y : ℝ | s < |y|} = Set.Ioi s ∪ Set.Iio (-s) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_Ioi, Set.mem_Iio]
    rw [lt_abs]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linarith)
  have hdisj : Disjoint (Set.Ioi s) (Set.Iio (-s)) := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    simp only [Set.mem_Ioi, Set.mem_Iio] at hy1 hy2
    linarith
  unfold tailGt combinedTail rightTail leftTail
  rw [hset, measure_union hdisj measurableSet_Iio,
    ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]

/-- At a positive threshold the two distinct endpoint atoms give the non-strict tail. -/
private theorem tailGe_eq_tailGt_add_atoms (μ : Measure ℝ) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0 < s) :
    tailGe μ s = tailGt μ s + (μ {s}).toReal + (μ {-s}).toReal := by
  have hset : {y : ℝ | s ≤ |y|} = {y : ℝ | s < |y|} ∪ ({s} ∪ {-s}) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro h
      rcases eq_or_lt_of_le h with h' | h'
      · have hy : y = s ∨ y = -s := (abs_eq hs.le).mp h'.symm
        rcases hy with hy | hy
        · exact Or.inr (Or.inl hy)
        · exact Or.inr (Or.inr hy)
      · exact Or.inl h'
    · rintro (h | h | h)
      · exact le_of_lt h
      · rw [h, abs_of_pos hs]
      · rw [h, abs_neg, abs_of_pos hs]
  have hdisj : Disjoint {y : ℝ | s < |y|} ({s} ∪ {-s}) := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    rcases hy2 with hy2 | hy2
    · rw [Set.mem_singleton_iff] at hy2
      rw [hy2] at hy1
      change s < |s| at hy1
      rw [abs_of_pos hs] at hy1
      exact lt_irrefl _ hy1
    · rw [Set.mem_singleton_iff] at hy2
      rw [hy2] at hy1
      change s < |-s| at hy1
      rw [abs_neg, abs_of_pos hs] at hy1
      exact lt_irrefl _ hy1
  have hmeas : MeasurableSet ({s} ∪ {-s} : Set ℝ) :=
    (measurableSet_singleton s).union (measurableSet_singleton (-s))
  have hunion : (μ ({s} ∪ {-s} : Set ℝ)).toReal
      = (μ {s}).toReal + (μ {-s}).toReal := by
    rw [measure_union (by
      rw [Set.disjoint_left]
      intro y hy1 hy2
      rw [Set.mem_singleton_iff] at hy1 hy2
      rw [hy1] at hy2
      exact absurd hy2 (by intro h; linarith [hs])) (measurableSet_singleton (-s)),
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  have hge : tailGe μ s = tailGt μ s + ((μ {s}).toReal + (μ {-s}).toReal) := by
    unfold tailGe tailGt
    rw [hset, measure_union hdisj hmeas,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hunion]
  simpa only [add_assoc] using hge

/-- The non-strict absolute tail adds both endpoint atoms to the canonical strict tail. -/
theorem tailGe_eq_combinedTail_add_atoms (μ : Measure ℝ) [IsFiniteMeasure μ]
    {s : ℝ} (hs : 0 < s) :
    tailGe μ s = combinedTail μ s + (μ {s}).toReal + (μ {-s}).toReal := by
  rw [tailGe_eq_tailGt_add_atoms μ hs, tailGt_eq_combinedTail μ hs.le]

/-- Right-tail difference equals the mass of the half-open interval. -/
private theorem rightTail_sub_eq {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hab : a ≤ b) :
    rightTail μ a - rightTail μ b = (μ (Set.Ioc a b)).toReal := by
  have hunion : Set.Ioi a = Set.Ioi b ∪ Set.Ioc a b := by
    ext y
    simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro h
      by_cases h' : b < y
      · exact Or.inl h'
      · exact Or.inr ⟨h, not_lt.mp h'⟩
    · rintro (h | h) <;> linarith
  have hdisj : Disjoint (Set.Ioi b) (Set.Ioc a b) := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    exact absurd (lt_of_lt_of_le hy1 hy2.2) (lt_irrefl _)
  have h : μ (Set.Ioi b ∪ Set.Ioc a b) = μ (Set.Ioi b) + μ (Set.Ioc a b) :=
    measure_union hdisj measurableSet_Ioc
  rw [← hunion] at h
  have h2 : (μ (Set.Ioi a)).toReal
      = ((μ (Set.Ioi b)) + (μ (Set.Ioc a b))).toReal := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h2
  unfold rightTail
  linarith [h2]

/-- A strict left-tail difference is the mass of the closed-open interval. -/
private theorem leftTail_sub_eq {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    (hab : a ≤ b) :
    leftTail μ a - leftTail μ b = (μ (Set.Ico (-b) (-a))).toReal := by
  have hunion : Set.Iio (-a) = Set.Iio (-b) ∪ Set.Ico (-b) (-a) :=
    (Set.Iio_union_Ico_eq_Iio (neg_le_neg hab)).symm
  have hdisj : Disjoint (Set.Iio (-b)) (Set.Ico (-b) (-a)) := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    exact (not_lt_of_ge hy2.1) hy1
  have h : (μ (Set.Iio (-a))).toReal =
      (μ (Set.Iio (-b))).toReal + (μ (Set.Ico (-b) (-a))).toReal := by
    rw [hunion, measure_union hdisj measurableSet_Ico,
      ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]
  unfold leftTail
  linarith [h]

/-- The atom at `s` is bounded by the drop of the combined tail on `[(1-δ)s, s]`. -/
private theorem atom_le_sub_combinedTail {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) :
    (μ {s}).toReal ≤ combinedTail μ ((1 - δ) * s) - combinedTail μ s := by
  have h1 : (1 - δ) * s ≤ s := by
    have h : (1 - δ) * s ≤ 1 * s :=
      mul_le_mul_of_nonneg_right (by linarith) hs.le
    simpa using h
  have h2 : (μ {s}).toReal ≤ rightTail μ ((1 - δ) * s) - rightTail μ s := by
    rw [rightTail_sub_eq h1]
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    apply Set.singleton_subset_iff.mpr
    exact ⟨by have hδs : 0 < δ * s := mul_pos hδ hs; nlinarith [hδs], le_refl _⟩
  have h3 : 0 ≤ leftTail μ ((1 - δ) * s) - leftTail μ s :=
    sub_nonneg.mpr (leftTail_antitone μ h1)
  unfold combinedTail
  linarith [h2, h3]

/-- For strict left tails, the negative endpoint atom is controlled by a drop below `s`. -/
private theorem atom_neg_le_sub_combinedTail {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {s δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) :
    (μ {-s}).toReal ≤ combinedTail μ ((1 - δ) * s) - combinedTail μ s := by
  have h1 : (1 - δ) * s ≤ s := by
    have h : (1 - δ) * s ≤ 1 * s :=
      mul_le_mul_of_nonneg_right (by linarith) hs.le
    simpa using h
  have h2 : (μ {-s}).toReal ≤ leftTail μ ((1 - δ) * s) - leftTail μ s := by
    rw [leftTail_sub_eq h1]
    apply ENNReal.toReal_mono (measure_ne_top μ _)
    apply measure_mono
    apply Set.singleton_subset_iff.mpr
    refine ⟨le_rfl, ?_⟩
    have hδs : 0 < δ * s := mul_pos hδ hs
    nlinarith [hδs]
  have h3 : 0 ≤ rightTail μ ((1 - δ) * s) - rightTail μ s :=
    sub_nonneg.mpr (rightTail_antitone μ h1)
  unfold combinedTail
  linarith [h2, h3]

/-! ### Tail-ratio limits -/

/-- For `0 < α`, the quantity `(1 - δ) ^ (-α)` can be made arbitrarily close to `1`
from above by taking `δ > 0` small. -/
private theorem exists_delta_rpow_neg {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ δ < 1 ∧ (1 - δ) ^ (-α) < 1 + ε := by
  have hα' : α ≠ 0 := hα.ne'
  have hcpos : (0:ℝ) < (1 + ε) ^ (-1 / α) := Real.rpow_pos_of_pos (by linarith) _
  have hclt : (1 + ε) ^ (-1 / α) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by linarith)
      (div_neg_of_neg_of_pos (by norm_num : (-1:ℝ) < 0) hα)
  use (1 - (1 + ε) ^ (-1 / α)) / 2
  refine ⟨by linarith, by linarith, ?_⟩
  have h1 : (1 + ε) = ((1 + ε) ^ (-1 / α)) ^ (-α) := by
    rw [← Real.rpow_mul (by linarith : (0:ℝ) ≤ 1 + ε)]
    rw [show (-1 / α) * (-α) = 1 by field_simp, Real.rpow_one]
  calc (1 - (1 - (1 + ε) ^ (-1 / α)) / 2) ^ (-α)
      < ((1 + ε) ^ (-1 / α)) ^ (-α) :=
        Real.rpow_lt_rpow_of_neg (by linarith) (by linarith) (by linarith)
    _ = 1 + ε := h1.symm

/-- For `0 < α`, the quantity `(1 + δ) ^ (-α)` can be made arbitrarily close to `1`
from below by taking `δ > 0` small. -/
private theorem exists_delta_rpow_pos {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ, 0 < δ ∧ 1 - ε < (1 + δ) ^ (-α) := by
  by_cases hε1 : ε < 1
  · have h1me : (0:ℝ) < 1 - ε := by linarith
    have h1me1 : (1:ℝ) - ε < 1 := by linarith
    have hcpos : (0:ℝ) < (1 - ε) ^ (-1 / α) := Real.rpow_pos_of_pos h1me _
    have hcgt : (1:ℝ) < (1 - ε) ^ (-1 / α) := by
      have h2 : (1 - ε) ^ (1 / α) < 1 :=
        Real.rpow_lt_one (by linarith) h1me1 (one_div_pos.mpr hα)
      have h3 : (1 - ε) ^ (-1 / α) = ((1 - ε) ^ (1 / α))⁻¹ := by
        rw [show (-1 / α) = -(1 / α) by ring, Real.rpow_neg (by linarith)]
      rw [h3]
      exact (one_lt_inv₀ (Real.rpow_pos_of_pos h1me _)).mpr h2
    use ((1 - ε) ^ (-1 / α) - 1) / 2
    refine ⟨by linarith, ?_⟩
    have h1 : ((1 - ε) ^ (-1 / α)) ^ (-α) = 1 - ε := by
      rw [← Real.rpow_mul (by linarith : (0:ℝ) ≤ 1 - ε)]
      rw [show (-1 / α) * (-α) = 1 by field_simp, Real.rpow_one]
    calc 1 - ε = ((1 - ε) ^ (-1 / α)) ^ (-α) := h1.symm
      _ < (1 + ((1 - ε) ^ (-1 / α) - 1) / 2) ^ (-α) :=
          Real.rpow_lt_rpow_of_neg (by linarith) (by linarith) (by linarith)
  · refine ⟨1, by norm_num, ?_⟩
    have hpos : (0:ℝ) < (1 + (1:ℝ)) ^ (-α) := Real.rpow_pos_of_pos (by norm_num) _
    linarith [hpos]

/-- If `W / T → 1` and `T` is eventually positive, then `W` is eventually positive. -/
private theorem eventually_pos_of_ratio_tendsto {W T : ℝ → ℝ}
    (hW : Tendsto (fun x => W x / T x) atTop (𝓝 1))
    (hTpos : ∀ᶠ x in atTop, 0 < T x) :
    ∀ᶠ x in atTop, 0 < W x := by
  have h1 : ∀ᶠ x in atTop, (1:ℝ) / 2 < W x / T x :=
    (tendsto_order.mp hW).1 (1 / 2) (by norm_num)
  filter_upwards [h1, hTpos] with x hx1 hx2
  rw [lt_div_iff₀ hx2] at hx1
  linarith [hx1, hx2]

/-- From `W / T → 1` and the ratio limit for `T`, deduce the ratio limit for `W`. -/
private theorem ratio_limit_of_ratio_tendsto {W T : ℝ → ℝ} {ρ : ℝ}
    (hW : Tendsto (fun x => W x / T x) atTop (𝓝 1))
    (hT : ∀ c > 0, Tendsto (fun x => T (c * x) / T x) atTop (𝓝 (c ^ ρ)))
    (hWpos : ∀ᶠ x in atTop, 0 < W x)
    (hTpos : ∀ᶠ x in atTop, 0 < T x) :
    ∀ c > 0, Tendsto (fun x => W (c * x) / W x) atTop (𝓝 (c ^ ρ)) := by
  intro c hc
  have hcT : Tendsto (fun x => c * x) atTop atTop := by
    have h := (tendsto_id (α := ℝ)).atTop_mul_const hc
    exact Filter.Tendsto.congr'
      (Filter.EventuallyEq.of_eq (funext fun x => mul_comm x c)) h
  have h1 : Tendsto (fun x => W (c * x) / T (c * x)) atTop (𝓝 1) := hW.comp hcT
  have h2 : Tendsto (fun x => T (c * x) / T x) atTop (𝓝 (c ^ ρ)) := hT c hc
  have h3 : Tendsto (fun x => T x / W x) atTop (𝓝 1) := by
    have h := hW.inv₀ (by norm_num : (1:ℝ) ≠ 0)
    have hEq : (fun x => (W x / T x)⁻¹) =ᶠ[atTop] (fun x => T x / W x) := by
      filter_upwards with x
      rw [inv_div]
    have h' := Filter.Tendsto.congr' hEq h
    simpa using h'
  have hprod := (h1.mul h2).mul h3
  have hEq : (fun x => (W (c * x) / T (c * x)) * (T (c * x) / T x) * (T x / W x))
      =ᶠ[atTop] (fun x => W (c * x) / W x) := by
    filter_upwards [hWpos, hTpos, Filter.Tendsto.eventually hcT hWpos,
      Filter.Tendsto.eventually hcT hTpos] with x hxW hxT hxWc hxTc
    have h1' : W (c * x) ≠ 0 := hxWc.ne'
    have h2' : T (c * x) ≠ 0 := hxTc.ne'
    have h3' : T x ≠ 0 := hxT.ne'
    have h4' : W x ≠ 0 := hxW.ne'
    field_simp
  have h' := Filter.Tendsto.congr' hEq hprod
  simpa using h'

/-- The upper tail is asymptotically the combined tail. -/
theorem tailGe_ratio_tendsto {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : ℝ}
    (hα : 0 < α) (hRV : IsRegularlyVarying (combinedTail μ) (-α)) :
    Tendsto (fun x => tailGe μ x / combinedTail μ x) atTop (𝓝 1) := by
  have hAtom : Tendsto (fun x => (μ {x}).toReal / combinedTail μ x) atTop (𝓝 0) := by
    rw [tendsto_order]
    constructor
    · intro b hb
      filter_upwards [hRV.eventually_pos] with x hx
      exact lt_of_lt_of_le hb (div_nonneg ENNReal.toReal_nonneg hx.le)
    · intro b hb
      obtain ⟨δ, hδ0, _hδ1, hδr⟩ := exists_delta_rpow_neg hα hb
      have hRatio : Tendsto (fun x => combinedTail μ ((1 - δ) * x) / combinedTail μ x)
          atTop (𝓝 ((1 - δ) ^ (-α))) := hRV.ratio_tendsto (by linarith)
      have hUp : ∀ᶠ x in atTop,
          combinedTail μ ((1 - δ) * x) / combinedTail μ x < 1 + b := by
        exact (tendsto_order.mp hRatio).2 (1 + b) (by linarith)
      have hLe : ∀ᶠ x in atTop,
          (μ {x}).toReal / combinedTail μ x
            ≤ combinedTail μ ((1 - δ) * x) / combinedTail μ x - 1 := by
        filter_upwards [hRV.eventually_pos, eventually_gt_atTop (0:ℝ)] with x hx hxpos
        have hA := atom_le_sub_combinedTail (μ := μ) (s := x) (δ := δ) hxpos hδ0
        rw [div_le_iff₀ hx]
        have hEq : (combinedTail μ ((1 - δ) * x) / combinedTail μ x - 1)
            * combinedTail μ x
            = combinedTail μ ((1 - δ) * x) - combinedTail μ x := by
          rw [sub_mul, div_mul_cancel₀ _ hx.ne', one_mul]
        rw [hEq]
        exact hA
      filter_upwards [hLe, hUp] with x hx1 hx2
      linarith [hx1, hx2]
  have hAtomNeg : Tendsto (fun x => (μ {-x}).toReal / combinedTail μ x) atTop (𝓝 0) := by
    rw [tendsto_order]
    constructor
    · intro b hb
      filter_upwards [hRV.eventually_pos] with x hx
      exact lt_of_lt_of_le hb (div_nonneg ENNReal.toReal_nonneg hx.le)
    · intro b hb
      obtain ⟨δ, hδ0, _hδ1, hδr⟩ := exists_delta_rpow_neg hα hb
      have hRatio : Tendsto (fun x => combinedTail μ ((1 - δ) * x) / combinedTail μ x)
          atTop (𝓝 ((1 - δ) ^ (-α))) := hRV.ratio_tendsto (by linarith)
      have hUp : ∀ᶠ x in atTop,
          combinedTail μ ((1 - δ) * x) / combinedTail μ x < 1 + b := by
        exact (tendsto_order.mp hRatio).2 (1 + b) (by linarith)
      have hLe : ∀ᶠ x in atTop,
          (μ {-x}).toReal / combinedTail μ x
            ≤ combinedTail μ ((1 - δ) * x) / combinedTail μ x - 1 := by
        filter_upwards [hRV.eventually_pos, eventually_gt_atTop (0:ℝ)] with x hx hxpos
        have hA := atom_neg_le_sub_combinedTail (μ := μ) (s := x) (δ := δ) hxpos hδ0
        rw [div_le_iff₀ hx]
        have hEq : (combinedTail μ ((1 - δ) * x) / combinedTail μ x - 1)
            * combinedTail μ x
            = combinedTail μ ((1 - δ) * x) - combinedTail μ x := by
          rw [sub_mul, div_mul_cancel₀ _ hx.ne', one_mul]
        rw [hEq]
        exact hA
      filter_upwards [hLe, hUp] with x hx1 hx2
      linarith [hx1, hx2]
  have hEq : (fun x => tailGe μ x / combinedTail μ x)
      =ᶠ[atTop] (fun x => 1 + (μ {x}).toReal / combinedTail μ x
        + (μ {-x}).toReal / combinedTail μ x) := by
    filter_upwards [hRV.eventually_pos, eventually_gt_atTop (0 : ℝ)] with x hx hxpos
    rw [tailGe_eq_combinedTail_add_atoms μ hxpos, add_div, add_div, div_self hx.ne']
  have hlim : Tendsto (fun x => 1 + (μ {x}).toReal / combinedTail μ x
      + (μ {-x}).toReal / combinedTail μ x) atTop (𝓝 (1 + 0 + 0)) :=
    (tendsto_const_nhds.add hAtom).add hAtomNeg
  have h' := Filter.Tendsto.congr' hEq.symm hlim
  simpa using h'

/-- The lower tail is asymptotically the combined tail. -/
theorem tailGt_ratio_tendsto {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : ℝ}
    (hRV : IsRegularlyVarying (combinedTail μ) (-α)) :
    Tendsto (fun x => tailGt μ x / combinedTail μ x) atTop (𝓝 1) := by
  refine (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).congr' ?_
  filter_upwards [hRV.eventually_pos, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  rw [tailGt_eq_combinedTail μ hx0, div_self hx.ne']

theorem eventually_pos_tailGe {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : ℝ}
    (hα : 0 < α) (hRV : IsRegularlyVarying (combinedTail μ) (-α)) :
    ∀ᶠ x in atTop, 0 < tailGe μ x :=
  eventually_pos_of_ratio_tendsto (tailGe_ratio_tendsto hα hRV) hRV.eventually_pos

theorem eventually_pos_tailGt {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : ℝ}
    (hRV : IsRegularlyVarying (combinedTail μ) (-α)) :
    ∀ᶠ x in atTop, 0 < tailGt μ x :=
  eventually_pos_of_ratio_tendsto (tailGt_ratio_tendsto hRV) hRV.eventually_pos

theorem tailGe_ratio_limit {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : ℝ}
    (hα : 0 < α) (hRV : IsRegularlyVarying (combinedTail μ) (-α)) :
    ∀ c > 0, Tendsto (fun x => tailGe μ (c * x) / tailGe μ x) atTop (𝓝 (c ^ (-α))) := by
  intro c hc
  exact ratio_limit_of_ratio_tendsto (tailGe_ratio_tendsto hα hRV)
    (fun c hc => hRV.ratio_tendsto hc)
    (eventually_pos_tailGe hα hRV) hRV.eventually_pos c hc

theorem tailGt_ratio_limit {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : ℝ}
    (hRV : IsRegularlyVarying (combinedTail μ) (-α)) :
    ∀ c > 0, Tendsto (fun x => tailGt μ (c * x) / tailGt μ x) atTop (𝓝 (c ^ (-α))) := by
  intro c hc
  exact ratio_limit_of_ratio_tendsto (tailGt_ratio_tendsto hRV)
    (fun c hc => hRV.ratio_tendsto hc)
    (eventually_pos_tailGt hRV) hRV.eventually_pos c hc

/-! ### Layer cake -/

private theorem intervalIntegrable_tailGe_sqrt {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {x : ℝ} :
    IntervalIntegrable (fun t => tailGe μ (Real.sqrt t)) volume (0:ℝ) (x ^ 2) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (sq_nonneg x)]
  apply Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
  · exact ((antitone_tailGe μ).comp_monotone Real.sqrt_monotone).measurable.aestronglyMeasurable
  · apply Eventually.of_forall
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (tailGe_nonneg μ _)]
    exact tailGe_le_one μ _

/-- Layer-cake formula for the truncated second moment, in terms of the upper
tail `tailGe`. The term `x ^ 2 * tailGt μ x` removes the contribution
from points with `|y| > x`, which lie outside the closed truncation interval. -/
theorem layerCake {μ : Measure ℝ} [IsProbabilityMeasure μ] {x : ℝ} (hx : 0 ≤ x) :
    ∫ y in Set.Icc (-x) x, y ^ 2 ∂μ
      = 2 * (∫ t in (0:ℝ)..x, t * tailGe μ t) - x ^ 2 * tailGt μ x := by
  have hInt : Integrable (fun y : ℝ => y ^ 2) (μ.restrict (Set.Icc (-x) x)) :=
    (continuous_pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hNonneg : 0 ≤ᵐ[μ.restrict (Set.Icc (-x) x)] (fun y : ℝ => y ^ 2) :=
    ae_of_all _ (fun y => sq_nonneg y)
  have hLe : (fun y : ℝ => y ^ 2) ≤ᵐ[μ.restrict (Set.Icc (-x) x)] fun _ => x ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact sq_le_sq' (Set.mem_Icc.mp hy).1 (Set.mem_Icc.mp hy).2
  have hLayer : ∫ y in Set.Icc (-x) x, y ^ 2 ∂μ
      = ∫ t in Set.Ioc (0:ℝ) (x ^ 2),
          (μ.restrict (Set.Icc (-x) x)).real {a | t ≤ a ^ 2} :=
    Integrable.integral_eq_integral_Ioc_meas_le hInt hNonneg hLe
  have hSet : ∀ t ∈ Set.Ioc (0:ℝ) (x ^ 2),
      (μ.restrict (Set.Icc (-x) x)).real {a | t ≤ a ^ 2}
        = tailGe μ (Real.sqrt t) - tailGt μ x := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht.1
    have htx : t ≤ x ^ 2 := ht.2
    have hsqrt : Real.sqrt t ≤ x := by
      rw [Real.sqrt_le_left hx]
      exact htx
    have hmeas : MeasurableSet {a : ℝ | t ≤ a ^ 2} :=
      measurableSet_le measurable_const (measurable_id.pow_const 2)
    have hInter : {a : ℝ | t ≤ a ^ 2} ∩ Set.Icc (-x) x
        = {a : ℝ | Real.sqrt t ≤ |a|} \ {a : ℝ | x < |a|} := by
      ext a
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_sdiff]
      constructor
      · rintro ⟨h3, h1, h2⟩
        have habs : |a| ≤ x := abs_le.mpr ⟨h1, h2⟩
        have hsqrt_le : Real.sqrt t ≤ |a| := by
          rw [Real.sqrt_le_left (abs_nonneg a), sq_abs]
          exact h3
        exact ⟨hsqrt_le, not_lt.mpr habs⟩
      · rintro ⟨h1, h2⟩
        have habs : |a| ≤ x := not_lt.mp h2
        have hax := abs_le.mp habs
        have ht_le : t ≤ a ^ 2 := by
          have h := (Real.sqrt_le_left (abs_nonneg a)).mp h1
          rwa [sq_abs] at h
        exact ⟨ht_le, hax.1, hax.2⟩
    have hsub : {a : ℝ | x < |a|} ⊆ {a : ℝ | Real.sqrt t ≤ |a|} := by
      intro a ha
      exact le_trans hsqrt (le_of_lt ha)
    have hmeas2 : NullMeasurableSet {a : ℝ | x < |a|} μ :=
      (measurableSet_lt measurable_const continuous_abs.measurable).nullMeasurableSet
    have hdiff : (μ.restrict (Set.Icc (-x) x)) {a : ℝ | t ≤ a ^ 2}
        = (μ {a : ℝ | Real.sqrt t ≤ |a|}) - (μ {a : ℝ | x < |a|}) := by
      rw [Measure.restrict_apply hmeas, hInter,
        measure_sdiff hsub hmeas2 (measure_ne_top μ _)]
    show ((μ.restrict (Set.Icc (-x) x)) {a : ℝ | t ≤ a ^ 2}).toReal = _
    calc ((μ.restrict (Set.Icc (-x) x)) {a : ℝ | t ≤ a ^ 2}).toReal
        = ((μ {a : ℝ | Real.sqrt t ≤ |a|}) - (μ {a : ℝ | x < |a|})).toReal := by
          rw [hdiff]
      _ = (μ {a : ℝ | Real.sqrt t ≤ |a|}).toReal
          - (μ {a : ℝ | x < |a|}).toReal :=
          ENNReal.toReal_sub_of_le (measure_mono hsub) (measure_ne_top μ _)
      _ = tailGe μ (Real.sqrt t) - tailGt μ x := rfl
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hSet] at hLayer
  rw [← intervalIntegral.integral_of_le (show (0:ℝ) ≤ x ^ 2 by positivity)] at hLayer
  have hInt1 : IntervalIntegrable (fun t => tailGe μ (Real.sqrt t)) volume (0:ℝ) (x ^ 2) :=
    intervalIntegrable_tailGe_sqrt
  have hInt2 : IntervalIntegrable (fun _ => tailGt μ x) volume (0:ℝ) (x ^ 2) :=
    intervalIntegrable_const
  rw [intervalIntegral.integral_sub hInt1 hInt2,
    intervalIntegral.integral_const] at hLayer
  rw [sub_zero, smul_eq_mul] at hLayer
  have hSub : (∫ u in (0:ℝ)..x, tailGe μ (Real.sqrt (u ^ 2)) * (2 * u))
      = ∫ t in (0:ℝ)..(x ^ 2), tailGe μ (Real.sqrt t) := by
    have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (f := fun u : ℝ => u ^ 2) (f' := fun u : ℝ => 2 * u)
      (g := fun v : ℝ => tailGe μ (Real.sqrt v)) (a := 0) (b := x)
      (by exact (continuous_pow 2).continuousOn)
      (by intro u _hu; simpa using hasDerivAt_pow 2 u)
      (by intro u hu; have hu1 := hu.1; rw [min_eq_left hx] at hu1; positivity)
    rw [show (0:ℝ) ^ 2 = 0 by norm_num] at h
    exact h
  rw [← hSub] at hLayer
  have hCongr : (∫ u in (0:ℝ)..x, tailGe μ (Real.sqrt (u ^ 2)) * (2 * u))
      = ∫ u in (0:ℝ)..x, 2 * (u * tailGe μ u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu0 : (0:ℝ) ≤ u := by
      rw [Set.uIcc_of_le hx] at hu
      exact hu.1
    show tailGe μ (Real.sqrt (u ^ 2)) * (2 * u) = 2 * (u * tailGe μ u)
    rw [Real.sqrt_sq hu0]
    ring
  rw [hCongr, intervalIntegral.integral_const_mul] at hLayer
  exact hLayer

/-! ### Main theorem -/

/-- The corrected truncated-second-moment asymptotic: for a probability measure
on `ℝ` with regularly varying combined tail of index `-α`, `0 < α < 2`, the
ratio `(∫ y in Icc (-x) x, y ^ 2 ∂μ) / (x ^ 2 * combinedTail μ x)` tends to
`α / (2 - α)`.

Correction: `v1/Atlas/TheoryOfProbability/code/RegularVariation.lean` states
this with the constant `2 / (2 - α)`, which is wrong; the Pareto tail gives
`α / (2 - α)` (see the test file). -/
theorem truncatedMoment_tendsto {μ : Measure ℝ} [IsProbabilityMeasure μ] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2)
    (hRV : IsRegularlyVarying (combinedTail μ) (-α)) :
    Tendsto (fun x => (∫ y in Set.Icc (-x) x, y ^ 2 ∂μ) / (x ^ 2 * combinedTail μ x))
      atTop (𝓝 (α / (2 - α))) := by
  have hK : Tendsto
      (fun x => (∫ t in (0:ℝ)..x, t * tailGe μ t) / (x ^ 2 * tailGe μ x))
      atTop (𝓝 (1 / (2 - α))) := by
    have h := karamata_integral (W := tailGe μ) (β := 1) (ρ := -α)
      (antitone_tailGe μ) (fun t => tailGe_nonneg μ t) ⟨1, fun t => tailGe_le_one μ t⟩
      (eventually_pos_tailGe hα hRV) (tailGe_ratio_limit hα hRV)
      (by linarith : (-α) < 0) (by norm_num : (0:ℝ) ≤ 1)
      (by linarith : (0:ℝ) < 1 + 1 + -α)
    have hEq : (fun x => (∫ t in (0:ℝ)..x, t ^ (1:ℝ) * tailGe μ t)
          / (x ^ ((1:ℝ) + 1) * tailGe μ x))
        =ᶠ[atTop] (fun x => (∫ t in (0:ℝ)..x, t * tailGe μ t) / (x ^ 2 * tailGe μ x)) := by
      filter_upwards with x
      congr 1
      · apply intervalIntegral.integral_congr
        intro t _ht
        show t ^ (1:ℝ) * tailGe μ t = t * tailGe μ t
        rw [Real.rpow_one]
      · rw [show ((1:ℝ) + 1) = 2 by norm_num, Real.rpow_two]
    have h2 : (1:ℝ) / (1 + 1 + -α) = 1 / (2 - α) := by congr 1; ring
    rw [h2] at h
    exact Filter.Tendsto.congr' hEq h
  have hG : Tendsto (fun x => tailGe μ x / combinedTail μ x) atTop (𝓝 1) :=
    tailGe_ratio_tendsto hα hRV
  have hU : Tendsto (fun x => tailGt μ x / combinedTail μ x) atTop (𝓝 1) :=
    tailGt_ratio_tendsto hRV
  have hEq2 : (fun x => (∫ y in Set.Icc (-x) x, y ^ 2 ∂μ) / (x ^ 2 * combinedTail μ x))
      =ᶠ[atTop] (fun x => 2 * ((∫ t in (0:ℝ)..x, t * tailGe μ t) / (x ^ 2 * tailGe μ x))
          * (tailGe μ x / combinedTail μ x) - tailGt μ x / combinedTail μ x) := by
    filter_upwards [eventually_gt_atTop (0:ℝ), eventually_pos_tailGe hα hRV,
      hRV.eventually_pos] with x hx0 hxG hxT
    rw [layerCake hx0.le]
    have hx2 : (x:ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hx0.ne'
    have hGx : tailGe μ x ≠ 0 := hxG.ne'
    have hTx : combinedTail μ x ≠ 0 := hxT.ne'
    field_simp
  have hlim := ((tendsto_const_nhds (x := (2:ℝ))).mul hK).mul hG |>.sub hU
  have hα2' : (2:ℝ) - α ≠ 0 := by linarith
  have hconst : (2:ℝ) * (1 / (2 - α)) * 1 - 1 = α / (2 - α) := by
    field_simp
    ring
  rw [hconst] at hlim
  exact Filter.Tendsto.congr' hEq2.symm hlim

end MathlibExt.Probability.TruncatedMoment
