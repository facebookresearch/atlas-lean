/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Nonparametric.KernelDensity

/-!
# Tests for the kernel density estimator at a fixed bandwidth

Fixture: the box kernel `1_{[-1/2, 1/2]}` and an iid uniform `[0, 1]` sample, realized as the
coordinates of `Measure.pi`, with density version `1_{[0, 1]}` (`B = 1`). The checks are the
interior unbiasedness of `integral_kde_eq`, the persistent boundary bias `1/2` at `t = 0`
(this density version is discontinuous there), the variance bound `1 / (n h)` from
`variance_kde_le`, and the degenerate sample size `n = 0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace KDETest

/-- The box kernel on `[-1/2, 1/2]`. -/
noncomputable def boxK : ℝ → ℝ := Set.indicator (Set.Icc (-1 / 2 : ℝ) (1 / 2)) 1

/-- The uniform density on `[0, 1]` (this version is discontinuous at `0` and `1`). -/
noncomputable def unifDens : ℝ → ℝ := Set.indicator (Set.Icc (0 : ℝ) 1) 1

/-- `n` iid uniform `[0, 1]` coordinates. -/
noncomputable def unifSample (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ => volume.restrict (Set.Icc (0 : ℝ) 1)

instance isProbabilityMeasure_restrict_Icc_zero_one :
    IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]

instance isProbabilityMeasure_unifSample (n : ℕ) : IsProbabilityMeasure (unifSample n) := by
  unfold unifSample; infer_instance

private lemma measurable_boxK : Measurable boxK := measurable_one.indicator measurableSet_Icc

private lemma measurable_unifDens : Measurable unifDens :=
  measurable_one.indicator measurableSet_Icc

private lemma unifDens_nonneg (x : ℝ) : 0 ≤ unifDens x :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) x

private lemma unifDens_le_one (x : ℝ) : unifDens x ≤ 1 :=
  Set.indicator_le_self' (fun _ _ => zero_le_one) x

private lemma hasLaw_unifSample (n : ℕ) (i : Fin n) :
    HasLaw (fun x : Fin n → ℝ => x i)
      (volume.withDensity fun x => ENNReal.ofReal (unifDens x)) (unifSample n) := by
  have hdens : (fun x => ENNReal.ofReal (unifDens x)) = (Set.Icc (0 : ℝ) 1).indicator 1 := by
    ext x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
    · simp only [unifDens, Set.indicator_of_mem hx, Pi.one_apply, ENNReal.ofReal_one]
    · simp only [unifDens, Set.indicator_of_notMem hx, ENNReal.ofReal_zero]
  rw [hdens, withDensity_indicator measurableSet_Icc, withDensity_one]
  exact (measurePreserving_eval (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)) i).hasLaw

private lemma iIndepFun_unifSample (n : ℕ) :
    iIndepFun (fun (i : Fin n) (x : Fin n → ℝ) => x i) (unifSample n) :=
  iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id

private lemma boxK_sq : (fun u => boxK u ^ 2) = boxK := by
  ext u
  by_cases hu : u ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)
  · simp only [boxK, Set.indicator_of_mem hu, Pi.one_apply, one_pow]
  · simp only [boxK, Set.indicator_of_notMem hu]
    norm_num

private lemma integrable_boxK : Integrable boxK :=
  continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc

private lemma integrable_boxK_sq : Integrable fun u => boxK u ^ 2 := by
  rw [boxK_sq]
  exact integrable_boxK

private lemma integral_boxK : ∫ u, boxK u = 1 := by
  rw [boxK, integral_indicator_one measurableSet_Icc, Real.volume_real_Icc]
  norm_num

/-- Hypothesis `hX` holds for the fixture. -/
example (n : ℕ) (i : Fin n) :
    HasLaw (fun x : Fin n → ℝ => x i)
      (volume.withDensity fun x => ENNReal.ofReal (unifDens x)) (unifSample n) := by
  exact hasLaw_unifSample n i

/-- Hypothesis `hindep` holds for the fixture. -/
example (n : ℕ) : iIndepFun (fun (i : Fin n) (x : Fin n → ℝ) => x i) (unifSample n) := by
  exact iIndepFun_unifSample n

/-- `∫ K² = 1` for the box kernel. -/
example : ∫ u, boxK u ^ 2 = 1 := by
  rw [boxK_sq, integral_boxK]

/-- Non-vacuity of (a), interior point: when `[t - h/2, t + h/2] ⊆ [0, 1]` the estimator is
unbiased for `f(t) = 1`. Prove via `integral_kde_eq`. -/
example {n : ℕ} (hn : 0 < n) {h t : ℝ} (hh : 0 < h) (ht₀ : h / 2 ≤ t) (ht₁ : t + h / 2 ≤ 1) :
    ∫ x, kde boxK h x t ∂(unifSample n) = 1 := by
  refine (integral_kde_eq (X := fun i (x : Fin n → ℝ) => x i) hn measurable_unifDens
    unifDens_nonneg unifDens_le_one (hasLaw_unifSample n) measurable_boxK integrable_boxK hh
    t).trans ?_
  have hint : (fun u => boxK u * unifDens (t - h * u)) = boxK := by
    ext u
    by_cases hu : u ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2)
    · have hv : t - h * u ∈ Set.Icc (0 : ℝ) 1 := ⟨by nlinarith [hu.2], by nlinarith [hu.1]⟩
      simp only [boxK, unifDens, Set.indicator_of_mem hu, Set.indicator_of_mem hv,
        Pi.one_apply, mul_one]
    · simp only [boxK, Set.indicator_of_notMem hu, zero_mul]
  rw [hint, integral_boxK]

/-- Boundary, (a) at `t = 0`: for every `0 < h ≤ 2` the mean is `1/2`, while this version has
`f 0 = 1`. The bias stays at `-1/2` however small `h` is, because `f` is not continuous at `0`.
This is why continuity at `t` is needed for the excluded bias slice. Prove via `integral_kde_eq`. -/
example {n : ℕ} (hn : 0 < n) {h : ℝ} (hh : 0 < h) (hh2 : h ≤ 2) :
    ∫ x, kde boxK h x 0 ∂(unifSample n) = 1 / 2 := by
  refine (integral_kde_eq (X := fun i (x : Fin n → ℝ) => x i) hn measurable_unifDens
    unifDens_nonneg unifDens_le_one (hasLaw_unifSample n) measurable_boxK integrable_boxK hh
    0).trans ?_
  have hint :
      (fun u => boxK u * unifDens (0 - h * u)) = (Set.Icc (-1 / 2 : ℝ) 0).indicator 1 := by
    ext u
    by_cases hu : u ∈ Set.Icc (-1 / 2 : ℝ) 0
    · have hu' : u ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2) := ⟨hu.1, by linarith [hu.2]⟩
      have hv : 0 - h * u ∈ Set.Icc (0 : ℝ) 1 := ⟨by nlinarith [hu.2], by nlinarith [hu.1]⟩
      simp only [boxK, unifDens, Set.indicator_of_mem hu, Set.indicator_of_mem hu',
        Set.indicator_of_mem hv, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem hu]
      rcases lt_or_ge 0 u with hu0 | hu0
      · have hv : 0 - h * u ∉ Set.Icc (0 : ℝ) 1 := fun hv => by nlinarith [hv.1]
        simp only [unifDens, Set.indicator_of_notMem hv, mul_zero]
      · have hu' : u ∉ Set.Icc (-1 / 2 : ℝ) (1 / 2) := fun hu' => hu ⟨hu'.1, hu0⟩
        simp only [boxK, Set.indicator_of_notMem hu', zero_mul]
  rw [hint, integral_indicator_one measurableSet_Icc, Real.volume_real_Icc]
  norm_num

/-- Non-vacuity of (b): with `B = 1` and `∫ K² = 1` the bound is `1 / (n h)`. At fixed `h`
this does not vanish unless `n h → ∞`. Prove via `variance_kde_le`. -/
example {n : ℕ} (hn : 0 < n) {h : ℝ} (hh : 0 < h) (t : ℝ) :
    Var[fun x => kde boxK h x t; unifSample n] ≤ 1 / (n * h) := by
  refine (variance_kde_le (X := fun i (x : Fin n → ℝ) => x i) hn (iIndepFun_unifSample n)
    measurable_unifDens unifDens_nonneg unifDens_le_one (hasLaw_unifSample n) measurable_boxK
    integrable_boxK_sq hh t).trans_eq ?_
  rw [boxK_sq, integral_boxK, one_mul]

set_option linter.unusedVariables false in
/-- Boundary `n = 0`: the estimator is identically `0` (`(0 * h)⁻¹ = 0`), so its variance is `0`
and `integral_kde_eq` correctly requires `0 < n`. -/
example {h : ℝ} (hh : 0 < h) (t : ℝ) :
    Var[fun x => kde boxK h x t; unifSample 0] = 0 := by
  have hzero : (fun x : Fin 0 → ℝ => kde boxK h x t) = 0 := by
    ext x
    simp only [kde, Nat.cast_zero, zero_mul, inv_zero, Pi.zero_apply]
  rw [hzero, variance_zero]

end KDETest
