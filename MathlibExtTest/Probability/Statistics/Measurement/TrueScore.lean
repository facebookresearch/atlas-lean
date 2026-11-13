/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.TrueScore
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.Measurement

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.Measurement
open scoped MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- True-score error has conditional mean zero on a constant score. -/
theorem condExp_error_ae_zero_const {Ω : Type*}
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (hm : m ≤ mΩ)
    {μ : Measure Ω} [IsProbabilityMeasure μ] (c : ℝ) :
    μ[(fun _ => c) - μ[(fun _ => c) | m] | m] =ᵐ[μ] 0 :=
  condExp_sub_condExp_ae_eq_zero m hm (integrable_const c)

/-- The error integrates to zero on a constant score. -/
theorem condExp_error_integral_zero_const {Ω : Type*}
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (hm : m ≤ mΩ)
    {μ : Measure Ω} [IsProbabilityMeasure μ] (c : ℝ) :
    ∫ ω, ((fun _ : Ω => c) - μ[(fun _ : Ω => c) | m]) ω ∂μ = 0 :=
  integral_sub_condExp_eq_zero m hm (integrable_const c)

/-- True score and error are uncorrelated on a constant score. -/
theorem trueScore_error_cov_zero_const {Ω : Type*}
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (hm : m ≤ mΩ)
    {μ : Measure Ω} [IsProbabilityMeasure μ] (c : ℝ) :
    cov[μ[(fun _ => c) | m], (fun _ => c) - μ[(fun _ => c) | m]; μ] = 0 := by
  have hX : MemLp (fun _ => c) 2 μ := memLp_const c
  exact covariance_condExp_sub_condExp_eq_zero m hm hX

/-- The spread splits into true-score plus error spread on a constant score. -/
theorem variance_true_plus_error_const {Ω : Type*}
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (hm : m ≤ mΩ)
    {μ : Measure Ω} [IsProbabilityMeasure μ] (c : ℝ) :
    Var[(fun _ => c); μ]
      = Var[μ[(fun _ => c) | m]; μ]
        + Var[(fun _ => c) - μ[(fun _ => c) | m]; μ] := by
  have hX : MemLp (fun _ => c) 2 μ := memLp_const c
  exact variance_eq_variance_condExp_add_variance_sub_condExp m hm hX

/-- Three tau-equivalent items with unit true and error spreads have
alpha `3 / 4`, through the equal-error corollary. -/
theorem alpha_three_items_equal_errors {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Fin 3 → Ω → ℝ}
    {T : Ω → ℝ} {c : Fin 3 → ℝ} {E : Fin 3 → Ω → ℝ}
    (hX : ∀ i, X i = fun ω => T ω + c i + E i ω)
    (hT : MemLp T 2 μ) (hE : ∀ i, MemLp (E i) 2 μ)
    (hTE : ∀ i, cov[T, E i; μ] = 0)
    (hEE : ∀ i j, i ≠ j → cov[E i, E j; μ] = 0)
    (hVarT : Var[T; μ] = 1) (hVarE : ∀ i, Var[E i; μ] = 1) :
    coefficientAlpha μ X = 3 / 4 := by
  have hS : (∑ i, Var[E i; μ]) = 3 := by simp [hVarE]
  have h12 : Var[fun ω => ∑ i, X i ω; μ] = 12 := by
    have h := variance_sum_of_tauEquivalent μ hX hT hE hTE hEE
    rw [h, hVarT, hS]
    norm_num
  have hpos : 0 < Var[fun ω => ∑ i, X i ω; μ] := by
    rw [h12]
    norm_num
  have hmain := coefficientAlpha_eq_of_tauEquivalent_of_variance_eq μ hX hT hE hTE hEE
    (by decide) hpos 1 hVarE
  rw [hmain, hVarT]
  norm_num

/-- Three tau-equivalent items with unequal error spreads call the main
theorem directly: with true spread `1` and error spreads `4, 1, 1`, alpha
is `3 / 5`. -/
theorem alpha_three_items_unequal_errors {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Fin 3 → Ω → ℝ}
    {T : Ω → ℝ} {c : Fin 3 → ℝ} {E : Fin 3 → Ω → ℝ}
    (hX : ∀ i, X i = fun ω => T ω + c i + E i ω)
    (hT : MemLp T 2 μ) (hE : ∀ i, MemLp (E i) 2 μ)
    (hTE : ∀ i, cov[T, E i; μ] = 0)
    (hEE : ∀ i j, i ≠ j → cov[E i, E j; μ] = 0)
    (hVarT : Var[T; μ] = 1)
    (hE0 : Var[E 0; μ] = 4) (hE1 : Var[E 1; μ] = 1) (hE2 : Var[E 2; μ] = 1) :
    coefficientAlpha μ X = 3 / 5 := by
  have hS : (∑ i, Var[E i; μ]) = 6 := by
    rw [Fin.sum_univ_three, hE0, hE1, hE2]
    norm_num
  have h15 : Var[fun ω => ∑ i, X i ω; μ] = 15 := by
    have h := variance_sum_of_tauEquivalent μ hX hT hE hTE hEE
    rw [h, hVarT, hS]
    norm_num
  have hpos : 0 < Var[fun ω => ∑ i, X i ω; μ] := by
    rw [h15]
    norm_num
  have hmain := coefficientAlpha_eq_variance_div_of_tauEquivalent μ hX hT hE hTE hEE
    (by decide) hpos
  rw [hmain, h15, variance_const_mul, hVarT]
  norm_num

/-- Conditional correlated-error example: any three-item model
`Xᵢ = F + Eᵢ` with `Var F = 0`, every error covariance `1`, and unit item
spreads has alpha `1` and composite reliability ratio `0`. The moments are
hypotheses; no model realizing them is constructed here. -/
theorem alpha_one_ratio_zero_of_correlated_errors {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Fin 3 → Ω → ℝ}
    {F : Ω → ℝ} {E : Fin 3 → Ω → ℝ}
    (hX : ∀ i, X i = fun ω => F ω + E i ω)
    (hF : MemLp F 2 μ) (hE : ∀ i, MemLp (E i) 2 μ)
    (hTE : ∀ i, cov[F, E i; μ] = 0)
    (hφ : Var[F; μ] = 0)
    (hΘ : ∀ i j, cov[E i, E j; μ] = 1)
    (hitem : ∀ i, Var[X i; μ] = 1) :
    coefficientAlpha μ X = 1
      ∧ Var[fun ω => (3 : ℝ) * F ω; μ] / Var[fun ω => ∑ i, X i ω; μ] = 0 := by
  have hX' : ∀ i, X i = fun ω => (0 : ℝ) + 1 * F ω + E i ω := by
    intro i
    rw [hX i]
    funext ω
    ring
  have hV : Var[fun ω => ∑ i, X i ω; μ] = 9 := by
    have hsum := variance_sum_of_oneFactor μ hX' hF hE hTE
    simp only [hφ, hΘ] at hsum
    rw [mul_zero, zero_add] at hsum
    have h9 : (∑ _i : Fin 3, ∑ _j : Fin 3, (1 : ℝ)) = 9 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      norm_num
    rw [h9] at hsum
    exact hsum
  have hS : (∑ i, Var[X i; μ]) = 3 := by
    simp_rw [hitem]
    simp
  have hpos : 0 < Var[fun ω => ∑ i, X i ω; μ] := by
    rw [hV]
    norm_num
  have hA : coefficientAlpha μ X = 1 := by
    unfold coefficientAlpha
    rw [ite_eq_left ⟨by decide, hpos⟩, hS, hV]
    norm_num
  have hnum : Var[fun ω => (3 : ℝ) * F ω; μ] = 0 := by
    rw [variance_const_mul, hφ, mul_zero]
  have hR : Var[fun ω => (3 : ℝ) * F ω; μ] / Var[fun ω => ∑ i, X i ω; μ] = 0 := by
    rw [hnum, hV]
    norm_num
  exact ⟨hA, hR⟩

/-- Omega on the parameters of the correlated-error example above (unit
loadings, factor spread `0`, every error covariance `1`) is `0`. -/
theorem omega_zero_of_correlated_errors :
    coefficientOmega (fun _ : Fin 3 => (1 : ℝ)) 0 (fun _ _ => (1 : ℝ)) = 0 := by
  unfold coefficientOmega
  simp only [Fin.sum_univ_three]
  norm_num

/-- Conditional negative-alpha example: any two items with spreads `3 / 2` and
composite spread `1` (so their covariance is `-1`) have alpha `-4`. The
moments are hypotheses; no model realizing them is constructed here. -/
theorem alpha_neg_four_of_negative_cov {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Fin 2 → Ω → ℝ}
    (h0 : Var[X 0; μ] = 3 / 2) (h1 : Var[X 1; μ] = 3 / 2)
    (hV : Var[fun ω => ∑ i, X i ω; μ] = 1) :
    coefficientAlpha μ X = -4 := by
  have hS : (∑ i, Var[X i; μ]) = 3 := by
    rw [Fin.sum_univ_two, h0, h1]
    norm_num
  have hpos : 0 < Var[fun ω => ∑ i, X i ω; μ] := by
    rw [hV]
    norm_num
  unfold coefficientAlpha
  rw [ite_eq_left ⟨by decide, hpos⟩, hS, hV]
  norm_num

/-- A zero total spread is outside the alpha domain: alpha is `0`. -/
theorem alpha_zero_of_zero_total {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Fin 2 → Ω → ℝ}
    (hV : Var[fun ω => ∑ i, X i ω; μ] = 0) :
    coefficientAlpha μ X = 0 := by
  have hn : ¬ (2 ≤ 2 ∧ 0 < Var[fun ω => ∑ i, X i ω; μ]) := by
    intro h
    rw [hV] at h
    exact (lt_irrefl (0 : ℝ)) h.2
  unfold coefficientAlpha
  rw [ite_eq_right hn]

/-- A single item is outside the alpha domain: alpha is `0`. -/
theorem alpha_zero_of_single_item {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Fin 1 → Ω → ℝ} :
    coefficientAlpha μ X = 0 := by
  have hn : ¬ (2 ≤ 1 ∧ 0 < Var[fun ω => ∑ i, X i ω; μ]) := by
    intro h
    exact absurd h.1 (by decide)
  unfold coefficientAlpha
  rw [ite_eq_right hn]

/-- Conditional check, not a constructed witness: a cross-item error covariance
equal to `1` is nonzero. -/
theorem errors_cov_ne_zero_of_eq_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {E : Fin 2 → Ω → ℝ}
    (h : cov[E 0, E 1; μ] = 1) : cov[E 0, E 1; μ] ≠ 0 := by
  rw [h]
  norm_num

/-- Conditional check, not a constructed witness: a true-score/error covariance
equal to `1` is nonzero. -/
theorem true_error_cov_ne_zero_of_eq_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {T : Ω → ℝ} {E : Fin 2 → Ω → ℝ}
    (h : cov[T, E 0; μ] = 1) : cov[T, E 0; μ] ≠ 0 := by
  rw [h]
  norm_num

/-- On the T6 data (total spread `39`), omega is `12 / 13` and lies in
`[0, 1]` by the one-factor range theorem. -/
theorem omega_mem_Icc_T6 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Fin 3 → Ω → ℝ}
    {ν : Fin 3 → ℝ} {lam : Fin 3 → ℝ} {F : Ω → ℝ} {E : Fin 3 → Ω → ℝ}
    (hX : ∀ i, X i = fun ω => ν i + lam i * F ω + E i ω)
    (hF : MemLp F 2 μ) (hE : ∀ i, MemLp (E i) 2 μ)
    (hFE : ∀ i, cov[F, E i; μ] = 0)
    {φ : ℝ} {Θ : Fin 3 → Fin 3 → ℝ}
    (hφ : Var[F; μ] = φ) (hΘ : ∀ i j, cov[E i, E j; μ] = Θ i j)
    (hlam : ∑ i, lam i = 6) (hφ1 : φ = 1)
    (hS : ∑ i, ∑ j, Θ i j = 3) :
    coefficientOmega lam φ Θ = 12 / 13
      ∧ coefficientOmega lam φ Θ ∈ Set.Icc 0 1 := by
  have hcov3 : (∑ i, ∑ j, cov[E i, E j; μ]) = ∑ i, ∑ j, Θ i j :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hΘ i j))
  have hV : Var[fun ω => ∑ i, X i ω; μ] = 39 := by
    have hsum := variance_sum_of_oneFactor μ hX hF hE hFE
    rw [hsum, hφ, hlam, hφ1, hcov3, hS]
    norm_num
  have hpos : 0 < Var[fun ω => ∑ i, X i ω; μ] := by
    rw [hV]
    norm_num
  have hom : coefficientOmega lam φ Θ = 12 / 13 := by
    unfold coefficientOmega
    rw [hlam, hφ1, hS]
    norm_num
  have hmem : coefficientOmega lam φ Θ ∈ Set.Icc 0 1 :=
    coefficientOmega_mem_Icc μ hX hF hE hFE hφ hΘ hpos
  exact ⟨hom, hmem⟩

/-- Raw parameters outside any model give omega `2`, which is outside
`[0, 1]`: the model hypotheses matter. -/
theorem omega_two_of_raw_params :
    coefficientOmega (fun _ : Fin 1 => (1 : ℝ)) 1 (fun _ _ => (-1 / 2 : ℝ)) = 2
      ∧ (2 : ℝ) ∉ Set.Icc 0 1 := by
  have h2 : coefficientOmega (fun _ : Fin 1 => (1 : ℝ)) 1
      (fun _ _ => (-1 / 2 : ℝ)) = 2 := by
    unfold coefficientOmega
    simp only [Fin.sum_univ_one]
    norm_num
  have hnin : (2 : ℝ) ∉ Set.Icc 0 1 := by
    intro h
    rw [Set.mem_Icc] at h
    norm_num at h
  exact ⟨h2, hnin⟩

/-- The rho-equals-one endpoint: with positive total spread and zero error
spread, both omega and the spread ratio equal `1`. -/
theorem omega_one_ratio_one_of_zero_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Fin 2 → Ω → ℝ}
    {ν : Fin 2 → ℝ} {lam : Fin 2 → ℝ} {F : Ω → ℝ} {E : Fin 2 → Ω → ℝ}
    (hX : ∀ i, X i = fun ω => ν i + lam i * F ω + E i ω)
    (hF : MemLp F 2 μ) (hE : ∀ i, MemLp (E i) 2 μ)
    (hFE : ∀ i, cov[F, E i; μ] = 0)
    {φ : ℝ} {Θ : Fin 2 → Fin 2 → ℝ}
    (hφ : Var[F; μ] = φ) (hΘ : ∀ i j, cov[E i, E j; μ] = Θ i j)
    (hlam : ∑ i, lam i = 2) (hφ1 : φ = 1)
    (hS : ∑ i, ∑ j, Θ i j = 0) :
    coefficientOmega lam φ Θ = 1
      ∧ Var[fun ω => (∑ i, lam i) * F ω; μ] / Var[fun ω => ∑ i, X i ω; μ] = 1
      ∧ coefficientOmega lam φ Θ ∈ Set.Icc 0 1 := by
  have hcov0 : (∑ i, ∑ j, cov[E i, E j; μ]) = ∑ i, ∑ j, Θ i j :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hΘ i j))
  have hV : Var[fun ω => ∑ i, X i ω; μ] = 4 := by
    have hsum := variance_sum_of_oneFactor μ hX hF hE hFE
    rw [hsum, hφ, hlam, hφ1, hcov0, hS]
    norm_num
  have hpos : 0 < Var[fun ω => ∑ i, X i ω; μ] := by
    rw [hV]
    norm_num
  have hom : coefficientOmega lam φ Θ = 1 := by
    unfold coefficientOmega
    rw [hlam, hφ1, hS]
    norm_num
  have heq := coefficientOmega_eq_variance_div_variance μ hX hF hE hFE hφ hΘ hpos
  have hratio : Var[fun ω => (∑ i, lam i) * F ω; μ]
      / Var[fun ω => ∑ i, X i ω; μ] = 1 := by
    rw [← heq, hom]
  have hmem : coefficientOmega lam φ Θ ∈ Set.Icc 0 1 :=
    coefficientOmega_mem_Icc μ hX hF hE hFE hφ hΘ hpos
  exact ⟨hom, hratio, hmem⟩

/-- Conditional degenerate example: in any one-factor model with `∑ lam = 0`
and `∑ Θ = 0`, the total spread is `0`, so positivity fails, and the
totalized omega is `0`. -/
theorem omega_degenerate_zero_total_outside_domain {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Fin 2 → Ω → ℝ}
    {ν : Fin 2 → ℝ} {lam : Fin 2 → ℝ} {F : Ω → ℝ} {E : Fin 2 → Ω → ℝ}
    (hX : ∀ i, X i = fun ω => ν i + lam i * F ω + E i ω)
    (hF : MemLp F 2 μ) (hE : ∀ i, MemLp (E i) 2 μ)
    (hFE : ∀ i, cov[F, E i; μ] = 0)
    {φ : ℝ} {Θ : Fin 2 → Fin 2 → ℝ}
    (hΘ : ∀ i j, cov[E i, E j; μ] = Θ i j)
    (hlam : ∑ i, lam i = 0)
    (hS : ∑ i, ∑ j, Θ i j = 0) :
    Var[fun ω => ∑ i, X i ω; μ] = 0
      ∧ coefficientOmega lam φ Θ = 0
      ∧ ¬ 0 < Var[fun ω => ∑ i, X i ω; μ] := by
  have hcov0 : (∑ i, ∑ j, cov[E i, E j; μ]) = ∑ i, ∑ j, Θ i j :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hΘ i j))
  have hV : Var[fun ω => ∑ i, X i ω; μ] = 0 := by
    have hsum := variance_sum_of_oneFactor μ hX hF hE hFE
    rw [hsum, hlam, hcov0, hS]
    ring
  have h0 : (∑ i, lam i) ^ 2 * φ = 0 := by
    rw [hlam]
    ring
  have hD : (∑ i, lam i) ^ 2 * φ + ∑ i, ∑ j, Θ i j = 0 := by
    rw [h0, hS, add_zero]
  have hom : coefficientOmega lam φ Θ = 0 := by
    unfold coefficientOmega
    rw [hD, h0, div_zero]
  have hnpos : ¬ 0 < Var[fun ω => ∑ i, X i ω; μ] := by
    intro h
    rw [hV] at h
    exact (lt_irrefl (0 : ℝ)) h
  exact ⟨hV, hom, hnpos⟩

/-- The library rescaling invariance on a concrete one-item instance: loading
`2` with factor spread `1 / 4` gives the same omega, `1 / 2`, as loading `1`
with factor spread `1`. -/
theorem omega_rescaled_one_item :
    coefficientOmega (fun _ : Fin 1 => 2 * (1 : ℝ)) (1 / 2 ^ 2) (fun _ _ => (1 : ℝ))
      = 1 / 2
      ∧ coefficientOmega (fun _ : Fin 1 => (1 : ℝ)) 1 (fun _ _ => (1 : ℝ)) = 1 / 2 := by
  have h1 : coefficientOmega (fun _ : Fin 1 => (1 : ℝ)) 1 (fun _ _ => (1 : ℝ)) = 1 / 2 := by
    unfold coefficientOmega
    simp only [Fin.sum_univ_one]
    norm_num
  exact ⟨(omega_invariant_under_rescaling (fun _ : Fin 1 => (1 : ℝ)) 1
    (fun _ _ => (1 : ℝ)) 2 two_ne_zero).trans h1, h1⟩

end MathlibExtTest.Probability.Statistics.Measurement
