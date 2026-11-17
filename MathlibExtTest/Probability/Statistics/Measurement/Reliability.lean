/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.Reliability

/-!
# Reliability-of-a-sum tests

Boundary and contrast cases for `reliability_sum_spearmanBrown`. All three
are implications over moment hypotheses, as in the existing true-score
tests; no model realizing the moments is constructed.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.Measurement

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.Measurement
open scoped MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Boundary `k = 1`, `w = 0` (conditional on the moments): a single
noiseless item has reliability `1`.  This case is outside
`coefficientAlpha` (`2 <= k`), which is why the leaf uses `k >= 1`. -/
theorem reliability_sum_single_no_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Fin 1 → Ω → ℝ} {T : Ω → ℝ} {E : Fin 1 → Ω → ℝ}
    (hX : ∀ j, X j = fun ω => T ω + E j ω)
    (hT : MemLp T 2 μ) (hE : ∀ j, MemLp (E j) 2 μ)
    (hTE : ∀ j, cov[T, E j; μ] = 0)
    (hEE : ∀ i j, i ≠ j → cov[E i, E j; μ] = 0)
    {v : ℝ} (hv : 0 < v)
    (hVarT : Var[T; μ] = v) (hVarE : ∀ j, Var[E j; μ] = 0) :
    Var[fun ω => (1 : ℝ) * T ω; μ] / Var[fun ω => ∑ j, X j ω; μ] = 1 := by
  have hmain := MathlibExt.Probability.Statistics.Measurement.reliability_sum_spearmanBrown
    μ (le_refl 1) hX hT hE hTE hEE hv (le_refl (0:ℝ)) hVarT hVarE
  simp only [Nat.cast_one] at hmain
  unfold MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables.attenuationFactor at hmain
  rw [hmain]
  have hv_ne : v + (0:ℝ) ≠ 0 := by
    have : v ≠ 0 := ne_of_gt hv
    simpa using this
  field_simp
  ring

/-- Three uncorrelated errors (conditional on the moments
`Var[T] = 1`, `Var[E j] = 1`): reliability of the sum is `3 / 4`;
one-item `rho = 1 / 2`, Spearman-Brown `3 * (1/2) / (1 + 2 * (1/2))`. -/
theorem reliability_sum_three_uncorrelated {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Fin 3 → Ω → ℝ} {T : Ω → ℝ} {E : Fin 3 → Ω → ℝ}
    (hX : ∀ j, X j = fun ω => T ω + E j ω)
    (hT : MemLp T 2 μ) (hE : ∀ j, MemLp (E j) 2 μ)
    (hTE : ∀ j, cov[T, E j; μ] = 0)
    (hEE : ∀ i j, i ≠ j → cov[E i, E j; μ] = 0)
    (hVarT : Var[T; μ] = 1) (hVarE : ∀ j, Var[E j; μ] = 1) :
    Var[fun ω => (3 : ℝ) * T ω; μ] / Var[fun ω => ∑ j, X j ω; μ] = 3 / 4 := by
  have hk : 1 ≤ 3 := by decide
  have hv : (0:ℝ) < 1 := by norm_num
  have hw : (0:ℝ) ≤ 1 := by norm_num
  have hmain := MathlibExt.Probability.Statistics.Measurement.reliability_sum_spearmanBrown
    μ hk hX hT hE hTE hEE hv hw hVarT hVarE
  norm_num at hmain ⊢
  unfold MathlibExt.Probability.Statistics.LinearModel.ErrorsInVariables.attenuationFactor at hmain
  rw [hmain]
  norm_num

/-- Same marginals, shared error (conditional on the moments
`Var[T] = 1` and every error covariance, diagonal included, `= 1`,
so `hEE` of the main theorem fails): reliability stays at the
one-item value `1 / 2`, not `3 / 4`.  Pins that `hEE` matters. -/
theorem reliability_sum_three_shared_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Fin 3 → Ω → ℝ} {T : Ω → ℝ} {E : Fin 3 → Ω → ℝ}
    (hX : ∀ j, X j = fun ω => T ω + E j ω)
    (hT : MemLp T 2 μ) (hE : ∀ j, MemLp (E j) 2 μ)
    (hTE : ∀ j, cov[T, E j; μ] = 0)
    (hEEcov : ∀ i j, cov[E i, E j; μ] = 1)
    (hVarT : Var[T; μ] = 1) :
    Var[fun ω => (3 : ℝ) * T ω; μ] / Var[fun ω => ∑ j, X j ω; μ] = 1 / 2 := by
  have hnum : Var[fun ω => (3 : ℝ) * T ω; μ] = 9 := by
    rw [variance_const_mul, hVarT]
    norm_num
  have hXmem : ∀ i, MemLp (X i) 2 μ := fun i => by
    have hfun : (fun ω => T ω + E i ω) = T + E i := rfl
    rw [hX i, hfun]
    exact hT.add (hE i)
  have hcov : ∀ i j, cov[X i, X j; μ] = Var[T; μ] + cov[E i, E j; μ] := by
    intro i j
    have hXi : X i = T + E i := by
      have hfun : (fun ω => T ω + E i ω) = T + E i := rfl
      rw [hX i, hfun]
    have hXj : X j = T + E j := by
      have hfun : (fun ω => T ω + E j ω) = T + E j := rfl
      rw [hX j, hfun]
    rw [hXi, hXj]
    have hXj_mem : MemLp (T + E j) 2 μ := hT.add (hE j)
    rw [covariance_add_left hT (hE i) hXj_mem]
    have h1 : cov[T, T + E j; μ] = cov[T, T; μ] + cov[T, E j; μ] :=
      covariance_add_right hT hT (hE j)
    have h2 : cov[E i, T + E j; μ] = cov[E i, T; μ] + cov[E i, E j; μ] :=
      covariance_add_right (hE i) hT (hE j)
    rw [h1, h2, hTE j]
    have hEiT : cov[E i, T; μ] = 0 := by rw [covariance_comm]; exact hTE i
    rw [hEiT, covariance_self hT.aemeasurable]
    ring
  have hden : Var[fun ω => ∑ j, X j ω; μ] = 18 := by
    rw [variance_fun_sum hXmem]
    have hpair : ∀ i j : Fin 3, cov[X i, X j; μ] = 2 := by
      intro i j
      rw [hcov i j, hVarT, hEEcov i j]
      norm_num
    have h1 : (∑ i, ∑ j, cov[X i, X j; μ]) = ∑ i : Fin 3, ∑ j : Fin 3, (2:ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hpair i j
    rw [h1]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  rw [hnum, hden]
  norm_num

end MathlibExtTest.Probability.Statistics.Measurement
