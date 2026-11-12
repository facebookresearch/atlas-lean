/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.ProcessVariance

@[expose] public section

open MeasureTheory Finset Filter Topology
open MathlibExt.Probability.Statistics.CountingProcess
open MathlibExt.Probability.Statistics.ProcessVariance

namespace MathlibExtTest.Probability.Statistics.ProcessVariance

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### The variance sum, computed from its definition -/

/-- Two subjects at risk (`n = 2`, `Y ≡ 2`), hazard increments `1/4`: two steps contribute
`2 · 2⁻¹ · (1/4)(3/4) = 3/16` each. -/
example (ω : Ω) : naVarianceSum 2 (fun _ _ => (2 : ℝ)) (fun i => (i : ℝ) / 4) 2 ω = 3 / 8 := by
  simp [naVarianceSum, sum_range_succ]; norm_num

/-- **Jump boundary.** With a discrete hazard the factor `1 - Δα` is genuine: the same data give
`3/8`, not the continuous-hazard value `∑ Δα / (Y / n) = 1/2`. -/
example (ω : Ω) : naVarianceSum 2 (fun _ _ => (2 : ℝ)) (fun i => (i : ℝ) / 4) 2 ω ≠
    ∑ i ∈ range 2, (((i + 1 : ℕ) : ℝ) / 4 - (i : ℝ) / 4) / ((2 : ℝ) / 2) := by
  simp [naVarianceSum, sum_range_succ]; norm_num

/-- **Vanishing-risk boundary.** An empty risk set contributes nothing (totalized inverse). -/
example (n k : ℕ) (α : ℕ → ℝ) (ω : Ω) : naVarianceSum n (fun _ _ => (0 : ℝ)) α k ω = 0 := by
  simp [naVarianceSum]

/-! ### The scaled Nelson–Aalen martingale -/

/-- One subject, one death in the first step, hazard increment `1/2`, `n = 4`:
`√4 (Â₁ - Λ*₁) = 2 (1 - 1/2) = 1`. -/
example (ω : Ω) : naScaledMartingale 4 (fun k _ => if k = 0 then 0 else 1) (fun _ _ => 1)
    (fun i => (i : ℝ) / 2) 1 ω = 1 := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp [naScaledMartingale, nelsonAalenProcess, restrictedHazard, stochasticIntegral, h4]
  norm_num

/-- The scaled martingale starts at `0`. -/
example (n : ℕ) (N Y : ℕ → Ω → ℝ) (α : ℕ → ℝ) (ω : Ω) : naScaledMartingale n N Y α 0 ω = 0 := by
  simp [naScaledMartingale, nelsonAalenProcess, restrictedHazard]

/-! ### The grid -/

example : gridIndex 1 (1 / 3) = 3 := by
  norm_num [gridIndex]

/-- A time strictly between grid points rounds down: `⌊(1/2) / (1/3)⌋ = 1`. -/
example : gridIndex (1 / 2) (1 / 3) = 1 := by
  rw [gridIndex, Nat.floor_eq_iff (by norm_num)]; norm_num

example : gridHazard id (1 / 4) 3 = 3 / 4 := by
  norm_num [gridHazard]

/-! ### The limit `∫_{(0, t]} dΛ / y` -/

/-- With `Λ(s) = s` and `y ≡ 1` the limit variance is `t`, computed from the Stieltjes measure. -/
theorem integral_id_one {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in Set.Ioc 0 t, ((fun _ : ℝ => (1 : ℝ)) s)⁻¹ ∂StieltjesFunction.id.measure = t := by
  simp [measureReal_def, StieltjesFunction.measure_Ioc, ht]

/-- Non-vacuity of the grid limit: unit hazard rate and `y ≡ 1`, so the Riemann–Stieltjes sums of
`dΛ / y` converge to `t`. -/
example {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    Tendsto (fun n : ℕ => ∑ i ∈ range (gridIndex t (1 / (n : ℕ))),
      (gridHazard StieltjesFunction.id (1 / (n : ℕ)) (i + 1) -
        gridHazard StieltjesFunction.id (1 / (n : ℕ)) i) /
          (fun _ : ℝ => (1 : ℝ)) (((i + 1 : ℕ) : ℝ) * (1 / (n : ℕ)))) atTop (𝓝 t) := by
  have h := tendsto_gridSum_integral StieltjesFunction.id continuous_id one_pos ht one_pos
    continuousOn_const (fun _ _ => le_rfl) tendsto_id
  rwa [integral_id_one ht.1] at h

/-- The mesh condition for the unit hazard rate. -/
example {t : ℝ} (ht : t ∈ Set.Icc 0 1) : ∀ᶠ n : ℕ in atTop, ∀ i < gridIndex t (1 / (n : ℕ)),
    gridHazard StieltjesFunction.id (1 / (n : ℕ)) (i + 1) -
      gridHazard StieltjesFunction.id (1 / (n : ℕ)) i ≤ 1 / 10 :=
  eventually_gridHazard_increment_le StieltjesFunction.id continuous_id one_pos ht tendsto_id _
    (by norm_num)

/-! ### Joint satisfiability of the headline hypotheses -/

/-- All hypotheses of the headline theorem hold together in a degenerate model: zero hazard
(`Λ ≡ 0`), no events, `n` subjects always at risk, `y ≡ 1`. Its conclusion is that the predictable
variation tends to `∫ dΛ / y = 0`. (The non-degenerate pieces are exercised above: the grid limit
for `Λ(s) = s`, and the binomial conditional variance is derived for a genuine single-subject model
in `condExp_sq_increment_of_hasUnitJumps`.) -/
example [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    TendstoInMeasure μ (fun n => predictableQuadraticVariation μ ℱ
      (naScaledMartingale n (fun _ _ => 0) (fun _ _ => (n : ℝ))
        (gridHazard (StieltjesFunction.const ℝ 0) (1 / (n : ℕ)))) (gridIndex t (1 / (n : ℕ))))
      atTop (fun _ => 0) := by
  have h := tendstoInMeasure_predictableQuadraticVariation_naScaledMartingale_integral
    (μ := μ) (ℱ := fun _ => ℱ) (N := fun _ _ _ => 0) (Y := fun n _ _ => (n : ℝ))
    (StieltjesFunction.const ℝ 0) continuous_const (y := fun _ => 1) one_pos ht one_pos
    continuousOn_const (fun _ _ => le_rfl) tendsto_id
    (fun _ => .of_measurable_add_one stronglyMeasurable_const fun _ => stronglyMeasurable_const)
    (fun n _ _ => by
      rcases Nat.eq_zero_or_pos n with h | h
      · left; simp [h]
      · right; exact_mod_cast h)
    (fun n j => by simp [aalenCompensator, stochasticIntegral, gridHazard])
    (fun n j => by simp [aalenCompensator, stochasticIntegral, gridHazard])
    (fun δ hδ => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      symm
      convert measure_empty (μ := μ)
      ext ω
      simp [hn', hδ.not_gt])
  simpa [StieltjesFunction.measure_const] using h
end MathlibExtTest.Probability.Statistics.ProcessVariance
