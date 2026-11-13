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

/-! ### The scaled Nelson–Aalen process -/

/-- One subject, one death in the first step, hazard increment `1/2`, `n = 4`:
`√4 (Â₁ - Λ*₁) = 2 (1 - 1/2) = 1`. -/
example (ω : Ω) : naScaledProcess 4 (fun k _ => if k = 0 then 0 else 1) (fun _ _ => 1)
    (fun i => (i : ℝ) / 2) 1 ω = 1 := by
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp [naScaledProcess, nelsonAalenProcess, restrictedHazard, stochasticIntegral, h4]
  norm_num

/-- The scaled process starts at `0`. -/
example (n : ℕ) (N Y : ℕ → Ω → ℝ) (α : ℕ → ℝ) (ω : Ω) : naScaledProcess n N Y α 0 ω = 0 := by
  simp [naScaledProcess, nelsonAalenProcess, restrictedHazard]

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

/-! ### The headline theorem on explicit models -/

/-- **Zero-hazard boundary.** With `Λ ≡ 0`, no events and `n` subjects always at risk, the
conditional square sum is identically `0` and the headline limit `∫ dΛ / y` is `0`. This is a
boundary case only; the non-degenerate instance is below. -/
example [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    TendstoInMeasure μ (fun n => predictableQuadraticVariation μ ℱ
      (naScaledProcess n (fun _ _ => 0) (fun _ _ => (n : ℝ))
        (gridHazard (StieltjesFunction.const ℝ 0) (1 / (n : ℕ)))) (gridIndex t (1 / (n : ℕ))))
      atTop (fun _ => 0) := by
  have h := tendstoInMeasure_predictableQuadraticVariation_naScaledProcess_integral
    (μ := μ) (ℱ := fun _ => ℱ) (N := fun _ _ _ => 0) (Y := fun n _ _ => (n : ℝ))
    (StieltjesFunction.const ℝ 0) continuous_const (y := fun _ => 1) one_pos ht one_pos
    continuousOn_const (fun _ _ => le_rfl) tendsto_id
    (fun _ => .of_measurable_add_one stronglyMeasurable_const fun _ => stronglyMeasurable_const)
    (fun n _ _ => by
      rcases Nat.eq_zero_or_pos n with h | h
      · left; simp [h]
      · right; exact_mod_cast h)
    (fun n j _ => by simp [aalenCompensator, stochasticIntegral, gridHazard])
    (fun n j _ => by simp [aalenCompensator, stochasticIntegral, gridHazard])
    (fun δ hδ => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      symm
      convert measure_empty (μ := μ)
      ext ω
      simp [hn', hδ.not_gt])
  simpa [StieltjesFunction.measure_const] using h
/-- The grid hazard increments of `Λ(s) = s` on mesh `1 / n`. -/
private noncomputable def dd (n j : ℕ) : ℝ :=
  gridHazard StieltjesFunction.id (1 / (n : ℕ)) (j + 1) -
    gridHazard StieltjesFunction.id (1 / (n : ℕ)) j

private lemma dd_eq (n j : ℕ) : dd n j = 1 / (n : ℝ) := by
  simp only [dd, gridHazard, StieltjesFunction.id_apply, id]; push_cast; ring

private lemma dd_mem (n j : ℕ) : 0 ≤ (n : ℝ) * dd n j * (1 - dd n j) := by
  rw [dd_eq]
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · have : (1 : ℝ) ≤ n := by exact_mod_cast h
    have h1 : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact this
    have h0 : 0 ≤ 1 / (n : ℝ) := by positivity
    have := mul_nonneg (mul_nonneg (Nat.cast_nonneg n) h0) (sub_nonneg.2 h1)
    simpa using this

/-- A deterministic compensated process whose squared increments are the binomial second moment
`n ΔΛ (1 - ΔΛ)`. -/
private noncomputable def MM (n j : ℕ) : ℝ :=
  ∑ i ∈ range j, Real.sqrt ((n : ℝ) * dd n i * (1 - dd n i))

/-- The `N` slot (not a counting process): `MM` plus the Aalen compensator of `Y ≡ n` under
`Λ(s) = s`. -/
private noncomputable def NN (n j : ℕ) (ω : Ω) : ℝ :=
  MM n j + aalenCompensator (fun _ _ => (n : ℝ)) (gridHazard StieltjesFunction.id (1 / (n : ℕ))) j ω

/-- At `t = 1` the grid of mesh `1 / n` has `n` steps, and the variance sum there is `1 - 1/n`,
computed from the definition: the discrete factor `1 - ΔΛ = 1 - 1/n` is visible at every `n` and
disappears in the limit. -/
example (n : ℕ) (hn : 0 < n) (ω : Ω) :
    gridIndex 1 (1 / (n : ℕ)) = n ∧
      naVarianceSum n (fun _ _ => (n : ℝ)) (gridHazard StieltjesFunction.id (1 / (n : ℕ))) n ω =
        1 - 1 / n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨by simp [gridIndex], ?_⟩
  have h := fun j => dd_eq n j
  simp only [dd] at h
  simp only [naVarianceSum, h, sum_const, card_range, nsmul_eq_mul]
  field_simp

/-- **Non-degenerate instance of the headline theorem**: unit hazard rate `Λ(s) = s`, `y ≡ 1`,
`t = 1`, `Y ≡ n`, increments with the binomial second moment; the limit is `∫_{(0,1]} ds = 1`.
The increments are deterministic and not a martingale: the headline theorem is a statement about
conditional square sums and does not assume one. -/
example [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) :
    TendstoInMeasure μ (fun n => predictableQuadraticVariation μ ℱ
      (naScaledProcess n (NN n) (fun _ _ => (n : ℝ))
        (gridHazard StieltjesFunction.id (1 / (n : ℕ)))) (gridIndex 1 (1 / (n : ℕ))))
      atTop (fun _ => 1) := by
  have hinc : ∀ n j, (fun ω : Ω => ((NN n (j + 1) ω - aalenCompensator (fun _ _ => (n : ℝ))
      (gridHazard StieltjesFunction.id (1 / (n : ℕ))) (j + 1) ω) -
      (NN n j ω - aalenCompensator (fun _ _ => (n : ℝ))
      (gridHazard StieltjesFunction.id (1 / (n : ℕ))) j ω)) ^ 2) =
      fun _ => (n : ℝ) * dd n j * (1 - dd n j) := by
    intro n j; funext ω
    simp only [NN, add_sub_cancel_right, MM, sum_range_succ, add_sub_cancel_left]
    exact Real.sq_sqrt (dd_mem n j)
  have h := tendstoInMeasure_predictableQuadraticVariation_naScaledProcess_integral
    (μ := μ) (ℱ := fun _ => ℱ) (N := fun n => NN n) (Y := fun n _ _ => (n : ℝ))
    StieltjesFunction.id continuous_id (y := fun _ => 1) one_pos
    (t := 1) ⟨zero_le_one, le_rfl⟩ one_pos
    continuousOn_const (fun _ _ => le_rfl) (K := fun n => n) tendsto_id
    (fun _ => .of_measurable_add_one stronglyMeasurable_const fun _ => stronglyMeasurable_const)
    (fun n _ _ => by
      rcases Nat.eq_zero_or_pos n with h | h
      · left; simp [h]
      · right; exact_mod_cast h)
    (fun n j _ => by rw [show _ = _ from hinc n j]; exact integrable_const _)
    (fun n j _ => by
      rw [show _ = _ from hinc n j, condExp_const (ℱ.le j)]
      exact Filter.EventuallyEq.rfl)
    (fun δ hδ => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      symm
      convert measure_empty (μ := μ)
      ext ω
      simp [hn', hδ.not_gt])
  rw [integral_id_one zero_le_one] at h
  exact h

end MathlibExtTest.Probability.Statistics.ProcessVariance
