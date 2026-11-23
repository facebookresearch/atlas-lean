/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.GenericChaining
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.Moments.Variance

/-!
# Generic chaining for Gaussian processes

A centred Gaussian process satisfies Talagrand's increment condition (2.4) for its canonical
distance `d(s, t) = (E(X_s - X_t)²)^{1/2}`, because each increment `X_s - X_t` is a centred
Gaussian variable of variance `d(s, t)²`. Hence the generic chaining bound gives
`E sup_t X_t ≤ 10 γ₂(T, d)` for every centred Gaussian process indexed by a finite set on which
the canonical distance is a metric: the upper half of the majorizing measure theorem.

A Gaussian process is encoded by its law on `T → ℝ`, which must be a Gaussian measure
(`ProbabilityTheory.IsGaussian`).

The canonical distance `canonicalDist` is the `L²(P)` norm of the increment, `eLpNorm` with
exponent `2`, so it is a genuine extended pseudo-distance: it is `∞` when an increment is not
square integrable. For square-integrable increments, which every Gaussian process has, it is
`(E(X_s - X_t)²)^{1/2}` computed with the Bochner integral (`canonicalDist_eq_ofReal_sqrt`).

## References

* M. Talagrand, *Upper and Lower Bounds for Stochastic Processes: Decomposition Theorems*,
  2nd ed., Ergebnisse 60, Springer 2021, (2.4), (2.113), Theorem 2.7.11 and the right-hand
  inequality of Theorem 2.10.1.
-/

@[expose] public section

namespace MathlibExt.Probability.GenericChaining

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- **Canonical distance of a process.** For random variables `(X_t)_{t ∈ T}`,
`d(s, t) = (E(X_s - X_t)²)^{1/2}` (Talagrand, *Upper and Lower Bounds for Stochastic Processes*,
2nd ed., 2021, (2.113)), the `L²(P)` norm of the increment `X_s - X_t`, as an extended-valued
distance function: it is `∞` when the increment is not square integrable, and for measurable
`X_t` it is a pseudo-distance (the triangle inequality of the `L²` norm). For square-integrable
increments it is the real formula (`canonicalDist_eq_ofReal_sqrt`). -/
noncomputable def canonicalDist {Ω T : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : T → Ω → ℝ) (s t : T) : ℝ≥0∞ :=
  eLpNorm (fun ω => X s ω - X t ω) 2 P

/-- **The canonical distance of square-integrable increments.** If `X_s - X_t ∈ L²(P)`, then
`canonicalDist P X s t = (E(X_s - X_t)²)^{1/2}`, with the expectation a Bochner integral. -/
theorem canonicalDist_eq_ofReal_sqrt {Ω T : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : T → Ω → ℝ} {s t : T} (h : MemLp (fun ω => X s ω - X t ω) 2 P) :
    canonicalDist P X s t = ENNReal.ofReal (Real.sqrt (∫ ω, (X s ω - X t ω) ^ 2 ∂P)) := by
  rw [canonicalDist, h.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    Real.sqrt_eq_rpow]
  congr 1
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs, one_div]

/-- **Two-sided Gaussian tail.** For `g ~ N(0, v)` and `u > 0`,
`P(|g| ≥ u) ≤ 2 exp(-u² / (2v))`, from the sub-Gaussian moment generating function. -/
theorem gaussianReal_abs_tail (v : ℝ≥0) {u : ℝ} (hu : 0 ≤ u) :
    (gaussianReal 0 v).real {y : ℝ | u ≤ |y|} ≤ 2 * Real.exp (-u ^ 2 / (2 * v)) := by
  have hmgf : HasSubgaussianMGF (fun y : ℝ => y) v (gaussianReal 0 v) :=
    ⟨fun t => integrable_exp_mul_gaussianReal t, fun t => by simp [mgf_fun_id_gaussianReal]⟩
  have h1 := hmgf.measure_ge_le hu
  have h2 := hmgf.neg.measure_ge_le hu
  have hsub : {y : ℝ | u ≤ |y|} ⊆ {y | u ≤ y} ∪ {y | u ≤ (-fun y : ℝ => y) y} := by
    intro y h
    rcases le_abs'.mp (show u ≤ |y| from h) with h | h
    · right; change u ≤ -y; linarith
    · left; exact h
  calc (gaussianReal 0 v).real {y : ℝ | u ≤ |y|}
      ≤ (gaussianReal 0 v).real ({y | u ≤ y} ∪ {y | u ≤ (-fun y : ℝ => y) y}) :=
        measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-u ^ 2 / (2 * v)) := by linarith

/-- **Increments of a centred Gaussian process** (Talagrand, *Upper and Lower Bounds for
Stochastic Processes*, 2nd ed., 2021, remark after (2.4)). If the law of `(X_t)_{t ∈ T}` on
`T → ℝ` is Gaussian and every `X_t` is integrable and centred, then for all `s, t` and `u > 0`,
`P(|X_s - X_t| ≥ u) ≤ 2 exp(-u² / (2 E(X_s - X_t)²))`. -/
theorem measureReal_abs_sub_ge_le_of_isGaussian {Ω T : Type*} [MeasurableSpace Ω] [Finite T]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : T → Ω → ℝ) (hX : ∀ t, Measurable (X t))
    (hG : IsGaussian (P.map fun ω t => X t ω)) (hint : ∀ t, Integrable (X t) P)
    (hcen : ∀ t, ∫ ω, X t ω ∂P = 0) (s t : T) {u : ℝ} (hu : 0 < u) :
    P.real {ω | u ≤ |X s ω - X t ω|} ≤
      2 * Real.exp (-u ^ 2 / (2 * ∫ ω, (X s ω - X t ω) ^ 2 ∂P)) := by
  set Y : Ω → T → ℝ := fun ω t => X t ω
  have hY : Measurable Y := Measurable.of_eval hX
  set L : StrongDual ℝ (T → ℝ) := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : T => ℝ) s -
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : T => ℝ) t
  have hLY : ∀ ω, L (Y ω) = X s ω - X t ω := fun ω => by simp [L, Y]
  have hmap := hG.map_eq_gaussianReal L
  have hS : MeasurableSet {y : ℝ | u ≤ |y|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hset : P.real {ω | u ≤ |X s ω - X t ω|} =
      ((P.map Y).map L).real {y : ℝ | u ≤ |y|} := by
    rw [measureReal_def, measureReal_def, Measure.map_apply L.continuous.measurable hS,
      Measure.map_apply hY (L.continuous.measurable hS)]
    rfl
  have hmean : (P.map Y)[L] = 0 := by
    rw [integral_map hY.aemeasurable L.continuous.aestronglyMeasurable]
    simp only [hLY]
    rw [integral_sub (hint s) (hint t), hcen, hcen, sub_zero]
  have hvar : Var[L; P.map Y] = ∫ ω, (X s ω - X t ω) ^ 2 ∂P := by
    rw [variance_map L.continuous.measurable.aemeasurable hY.aemeasurable,
      variance_eq_integral (L.continuous.measurable.comp hY).aemeasurable]
    have h0 : P[⇑L ∘ Y] = 0 := by
      rw [← hmean, integral_map hY.aemeasurable L.continuous.aestronglyMeasurable]; rfl
    rw [h0]
    simp only [sub_zero, Function.comp_apply, hLY]
  rw [hset, hmap, hmean, hvar]
  have htail := gaussianReal_abs_tail (∫ ω, (X s ω - X t ω) ^ 2 ∂P).toNNReal hu.le
  rwa [Real.coe_toNNReal _ (integral_nonneg fun ω => sq_nonneg _)] at htail

/-- **Generic chaining bound for Gaussian processes** (Talagrand, *Upper and Lower Bounds for
Stochastic Processes*, 2nd ed., 2021, Theorem 2.7.11 for Gaussian processes; the right-hand
inequality of the majorizing measure theorem, Theorem 2.10.1). Let `T` be a finite nonempty metric
space and `(X_t)_{t ∈ T}` a centred Gaussian process (Gaussian law on `T → ℝ`, `E X_t = 0`) whose
canonical distance is the metric: `d(s, t) = (E(X_s - X_t)²)^{1/2}`. Then
`E sup_{t ∈ T} X_t ≤ 10 γ₂(T, d)`. -/
theorem integral_iSup_le_gammaTwo_of_isGaussian {Ω T : Type*} [MeasurableSpace Ω]
    [MetricSpace T] [Finite T] [Nonempty T] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : T → Ω → ℝ) (hX : ∀ t, Measurable (X t)) (hG : IsGaussian (P.map fun ω t => X t ω))
    (hcen : ∀ t, ∫ ω, X t ω ∂P = 0)
    (hdist : ∀ s t, dist s t = Real.sqrt (∫ ω, (X s ω - X t ω) ^ 2 ∂P)) :
    ENNReal.ofReal (∫ ω, ⨆ t, X t ω ∂P) ≤ 10 * gammaFunctional 2 (edist : T → T → ℝ≥0∞) := by
  have := Fintype.ofFinite T
  have hY : Measurable fun ω (t : T) => X t ω := Measurable.of_eval hX
  have hint : ∀ t, Integrable (X t) P := fun t => by
    set Lt : StrongDual ℝ (T → ℝ) := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : T => ℝ) t
    have h := IsGaussian.integrable_dual (P.map fun ω t => X t ω) Lt
    exact (integrable_map_measure Lt.continuous.aestronglyMeasurable hY.aemeasurable).mp h
  refine integral_iSup_le_gammaTwo P X hX hint hcen fun s t u hu => ?_
  have h := measureReal_abs_sub_ge_le_of_isGaussian P X hX hG hint hcen s t hu
  rwa [hdist, Real.sq_sqrt (integral_nonneg fun ω => sq_nonneg _)]

/-- **The metric is the canonical distance.** If every increment `X_s - X_t` is square integrable
and `d(s, t) = (E(X_s - X_t)²)^{1/2}` for all `s, t`, then `edist = canonicalDist P X`, so `γ₂`
computed for the metric and for the canonical distance agree. -/
theorem edist_eq_canonicalDist {Ω T : Type*} [MeasurableSpace Ω] [MetricSpace T] (P : Measure Ω)
    (X : T → Ω → ℝ) (hX2 : ∀ s t, MemLp (fun ω => X s ω - X t ω) 2 P)
    (hdist : ∀ s t, dist s t = Real.sqrt (∫ ω, (X s ω - X t ω) ^ 2 ∂P)) :
    (edist : T → T → ℝ≥0∞) = canonicalDist P X := by
  funext s t
  rw [edist_dist, hdist, canonicalDist_eq_ofReal_sqrt (hX2 s t)]

/-- **Increments of a Gaussian process are square integrable.** If the law of `(X_t)_{t ∈ T}` on
`T → ℝ` is Gaussian, every increment `X_s - X_t` is in `L²(P)`, as the image of the law under a
continuous linear functional. -/
theorem memLp_sub_of_isGaussian {Ω T : Type*} [MeasurableSpace Ω] [Finite T] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : T → Ω → ℝ) (hX : ∀ t, Measurable (X t))
    (hG : IsGaussian (P.map fun ω t => X t ω)) (s t : T) :
    MemLp (fun ω => X s ω - X t ω) 2 P := by
  have := Fintype.ofFinite T
  set Y : Ω → T → ℝ := fun ω t => X t ω
  have hY : Measurable Y := Measurable.of_eval hX
  set L : StrongDual ℝ (T → ℝ) := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : T => ℝ) s -
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : T => ℝ) t
  have h := IsGaussian.memLp_dual (P.map Y) L 2 (by simp)
  exact (memLp_map_measure_iff L.continuous.aestronglyMeasurable hY.aemeasurable).mp h

/-- **Generic chaining bound for Gaussian processes, canonical form** (Talagrand, *Upper and Lower
Bounds for Stochastic Processes*, 2nd ed., 2021, the right-hand inequality of Theorem 2.10.1).
Under the hypotheses of `integral_iSup_le_gammaTwo_of_isGaussian`,
`E sup_{t ∈ T} X_t ≤ 10 γ₂(T, canonicalDist P X)`: the upper half of
`MathlibExt.Probability.MajorizingMeasureWanted.majorizing_measure`, with `L = 10`, when the
canonical distance is a metric on `T`. -/
theorem integral_iSup_le_gammaTwo_canonicalDist {Ω T : Type*} [MeasurableSpace Ω]
    [MetricSpace T] [Finite T] [Nonempty T] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : T → Ω → ℝ) (hX : ∀ t, Measurable (X t)) (hG : IsGaussian (P.map fun ω t => X t ω))
    (hcen : ∀ t, ∫ ω, X t ω ∂P = 0)
    (hdist : ∀ s t, dist s t = Real.sqrt (∫ ω, (X s ω - X t ω) ^ 2 ∂P)) :
    ENNReal.ofReal (∫ ω, ⨆ t, X t ω ∂P) ≤ 10 * gammaFunctional 2 (canonicalDist P X) := by
  rw [← edist_eq_canonicalDist P X (memLp_sub_of_isGaussian P X hX hG) hdist]
  exact integral_iSup_le_gammaTwo_of_isGaussian P X hX hG hcen hdist

end MathlibExt.Probability.GenericChaining
