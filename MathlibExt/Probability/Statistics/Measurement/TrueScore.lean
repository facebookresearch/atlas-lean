/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.Variance

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import MathlibExt.MeasureTheory.Function.ConditionalExpectation.BestPredictor

/-!
# Classical true-score theory with coefficient alpha and coefficient omega

D02.0: for a square-integrable score `X` and a sub-σ-algebra `m`, the true
score is the conditional expectation `μ[X | m]` and the error is
`X - μ[X | m]`. The error has conditional mean zero, hence mean zero; true
score and error are uncorrelated; the total spread splits into true-score
plus error spread. The spread here is Mathlib `variance`, defined as
`(evariance X μ).toReal`, so the L² hypothesis `MemLp X 2 μ` is the
operative integrability condition.

D02.4: Cronbach coefficient alpha (Cronbach 1951, as cited in Martinková
and Hladká, Eq. 4.13). The public `coefficientAlpha` is domain-guarded: it
agrees with the textbook `k / (k - 1) * (1 - ∑ item spreads / total spread)`
ratio when `2 ≤ k` and the total spread is positive, and is `0` outside that
domain. Under tau-equivalence with uncorrelated errors, alpha equals the
composite reliability ratio (see
`coefficientAlpha_eq_variance_div_of_tauEquivalent`), with the equal-error
case in `coefficientAlpha_eq_of_tauEquivalent_of_variance_eq`. Without the
zero-covariance model hypotheses, alpha can exceed the reliability ratio
under correlated errors (see
`alpha_one_ratio_zero_of_correlated_errors`) and can even be negative (see
`alpha_neg_four_of_negative_cov`).

D06.4: McDonald coefficient omega for a one-factor congeneric sum, with the
displayed `ω₁` formula taken from the semTools `reliability` documentation
(which cites Bollen 1980 and Raykov 2001). Under the full one-factor model
hypotheses with positive total spread, omega lies in `[0, 1]` (see
`coefficientOmega_mem_Icc`); the diagonal form (see
`coefficientOmega_eq_of_diagonal`) is pure algebra with no model. The error
covariance matrix `Θ` is meant to be symmetric; the double sum then equals
the displayed `∑ θᵢᵢ + 2 ∑_{i<j} θᵢⱼ` form. The factor scale is not
identified: rescaling loadings and factor spread leaves omega unchanged
(see `omega_invariant_under_rescaling`).

## References

- Martinková and Hladká, Chapter 4 (coefficient alpha, Eq. 4.8 and
  Eq. 4.13; alpha can be lower or greater than the reliability under
  correlated errors).
- Cronbach (1951), as cited in Martinková and Hladká, Eq. 4.13.
- semTools `reliability` documentation, source of the displayed `ω₁`
  formula, citing Bollen (1980) and Raykov (2001).
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.Measurement

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The error `X - μ[X | m]` has conditional mean zero given `m`. -/
theorem condExp_sub_condExp_ae_eq_zero {Ω : Type*}
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (hm : m ≤ mΩ)
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Integrable X μ) : μ[X - μ[X | m] | m] =ᵐ[μ] 0 := by
  have hc : Integrable μ[X | m] μ := integrable_condExp
  have h1 : μ[X - μ[X | m] | m] =ᵐ[μ] μ[X | m] - μ[μ[X | m] | m] :=
    condExp_sub hX hc m
  have h2 : μ[μ[X | m] | m] = μ[X | m] :=
    condExp_of_stronglyMeasurable hm stronglyMeasurable_condExp hc
  have h3 : μ[X | m] - μ[μ[X | m] | m] =ᵐ[μ] μ[X | m] - μ[X | m] := by
    rw [h2]
  have h4 : μ[X | m] - μ[X | m] =ᵐ[μ] (0 : Ω → ℝ) := by
    have h0 : μ[X | m] - μ[X | m] = 0 := sub_self _
    rw [h0]
  exact h1.trans (h3.trans h4)

/-- Mean-zero error: the error integrates to zero. -/
theorem integral_sub_condExp_eq_zero {Ω : Type*}
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (hm : m ≤ mΩ)
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Integrable X μ) : ∫ ω, (X - μ[X | m]) ω ∂μ = 0 := by
  have h2 : ∫ ω, (X - μ[X | m]) ω ∂μ = ∫ ω, μ[X - μ[X | m] | m] ω ∂μ :=
    (integral_condExp hm).symm
  have h3 : (∫ ω, μ[X - μ[X | m] | m] ω ∂μ) = ∫ ω, (0 : Ω → ℝ) ω ∂μ :=
    integral_congr_ae (condExp_sub_condExp_ae_eq_zero m hm hX)
  rw [h2, h3]
  simp

/-- Zero covariance between true score and error. -/
theorem covariance_condExp_sub_condExp_eq_zero {Ω : Type*}
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (hm : m ≤ mΩ)
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : MemLp X 2 μ) : cov[μ[X | m], X - μ[X | m]; μ] = 0 := by
  have hT : MemLp μ[X | m] 2 μ := hX.condExp one_le_two
  have hTi : Integrable X μ := hX.integrable (by simp)
  have hEmean : ∫ ω, (X - μ[X | m]) ω ∂μ = 0 :=
    integral_sub_condExp_eq_zero m hm hTi
  have hmem : MemLp (fun ω => μ[X | m] ω - ∫ a, μ[X | m] a ∂μ) 2 μ :=
    hT.sub (memLp_const _)
  have hmeas : StronglyMeasurable[m]
      (fun ω => μ[X | m] ω - ∫ a, μ[X | m] a ∂μ) :=
    stronglyMeasurable_condExp.sub stronglyMeasurable_const
  have key := MeasureTheory.integral_sub_condExp_mul_eq_zero hm hX hmem hmeas
  unfold covariance
  simp only [hEmean, sub_zero]
  have hpoint : (fun ω => (μ[X | m] ω - ∫ a, μ[X | m] a ∂μ) * (X - μ[X | m]) ω)
      = fun ω => (X ω - μ[X | m] ω) * (μ[X | m] ω - ∫ a, μ[X | m] a ∂μ) := by
    funext ω
    simp only [Pi.sub_apply]
    ring
  rw [hpoint]
  exact key

/-- Total spread splits into true-score plus error spread. -/
theorem variance_eq_variance_condExp_add_variance_sub_condExp {Ω : Type*}
    (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (hm : m ≤ mΩ)
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : MemLp X 2 μ) :
    Var[X; μ] = Var[μ[X | m]; μ] + Var[X - μ[X | m]; μ] := by
  have hT : MemLp μ[X | m] 2 μ := hX.condExp one_le_two
  have hE : MemLp (X - μ[X | m]) 2 μ := hX.sub hT
  have hcov : cov[μ[X | m], X - μ[X | m]; μ] = 0 :=
    covariance_condExp_sub_condExp_eq_zero m hm hX
  have hXeq : X = μ[X | m] + (X - μ[X | m]) := by
    funext ω
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  conv_lhs => rw [hXeq]
  rw [variance_add hT hE, hcov]
  ring

/-- D02.1 spread decomposition (private): for `X = T + E` with zero
covariance, `Var X = Var T + Var E`. -/
private theorem variance_add_of_cov_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {T E : Ω → ℝ}
    (hT : MemLp T 2 μ) (hE : MemLp E 2 μ) (hcov : cov[T, E; μ] = 0) :
    Var[T + E; μ] = Var[T; μ] + Var[E; μ] := by
  rw [variance_add hT hE, hcov]
  ring

/-- One-factor plumbing: each item is square-integrable. -/
private theorem memLp_X_of_oneFactor {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ} {X : Fin k → Ω → ℝ}
    {ν : Fin k → ℝ} {lam : Fin k → ℝ} {F : Ω → ℝ} {E : Fin k → Ω → ℝ}
    (hX : ∀ i, X i = fun ω => ν i + lam i * F ω + E i ω)
    (hF : MemLp F 2 μ) (hE : ∀ i, MemLp (E i) 2 μ) (i : Fin k) :
    MemLp (X i) 2 μ := by
  have hSi : MemLp (fun ω => lam i * F ω) 2 μ := hF.const_mul (lam i)
  have hC : MemLp (fun _ => ν i) 2 μ := memLp_const _
  rw [hX i]
  exact (hC.add hSi).add (hE i)

/-- One-factor plumbing: item covariance splits into common plus error part. -/
private theorem cov_X_of_oneFactor {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ} {X : Fin k → Ω → ℝ}
    {ν : Fin k → ℝ} {lam : Fin k → ℝ} {F : Ω → ℝ} {E : Fin k → Ω → ℝ}
    (hX : ∀ i, X i = fun ω => ν i + lam i * F ω + E i ω)
    (hF : MemLp F 2 μ) (hE : ∀ i, MemLp (E i) 2 μ)
    (hFE : ∀ i, cov[F, E i; μ] = 0)
    (i j : Fin k) :
    cov[X i, X j; μ] = lam i * lam j * Var[F; μ] + cov[E i, E j; μ] := by
  have hSi : MemLp (fun ω => lam i * F ω) 2 μ := hF.const_mul (lam i)
  have hSj : MemLp (fun ω => lam j * F ω) 2 μ := hF.const_mul (lam j)
  have hCi : MemLp (fun _ => ν i) 2 μ := memLp_const _
  have hCj : MemLp (fun _ => ν j) 2 μ := memLp_const _
  have hRj : MemLp ((fun _ => ν j) + ((fun ω => lam j * F ω) + E j)) 2 μ :=
    hCj.add (hSj.add (hE j))
  have eXi : X i = (fun _ => ν i) + ((fun ω => lam i * F ω) + E i) := by
    rw [hX i]
    funext ω
    simp only [Pi.add_apply]
    ring
  have eXj : X j = (fun _ => ν j) + ((fun ω => lam j * F ω) + E j) := by
    rw [hX j]
    funext ω
    simp only [Pi.add_apply]
    ring
  have hSS : cov[fun ω => lam i * F ω, fun ω => lam j * F ω; μ]
      = lam i * lam j * Var[F; μ] := by
    rw [covariance_const_mul_left, covariance_const_mul_right,
      covariance_self hF.aemeasurable]
    ring
  have hSE : cov[fun ω => lam i * F ω, E j; μ] = 0 := by
    rw [covariance_const_mul_left, hFE j, mul_zero]
  have hES : cov[E i, fun ω => lam j * F ω; μ] = 0 := by
    rw [covariance_const_mul_right, covariance_comm (E i) F, hFE i, mul_zero]
  rw [eXi, eXj, covariance_add_left hCi (hSi.add (hE i)) hRj,
    covariance_const_left, zero_add,
    covariance_add_right (hSi.add (hE i)) hCj (hSj.add (hE j)), covariance_const_right,
    zero_add, covariance_add_left hSi (hE i) (hSj.add (hE j)),
    covariance_add_right hSi hSj (hE j), covariance_add_right (hE i) hSj (hE j),
    hSS, hSE, hES, add_zero, zero_add]

/-- Tau-equivalence plumbing, derived from the one-factor case: each item is
square-integrable. -/
private theorem memLp_X_of_tauEquivalent {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ} {X : Fin k → Ω → ℝ}
    {T : Ω → ℝ} {c : Fin k → ℝ} {E : Fin k → Ω → ℝ}
    (hX : ∀ i, X i = fun ω => T ω + c i + E i ω)
    (hT : MemLp T 2 μ) (hE : ∀ i, MemLp (E i) 2 μ) (i : Fin k) :
    MemLp (X i) 2 μ := by
  have hX' : ∀ i, X i = fun ω => c i + 1 * T ω + E i ω := by
    intro i
    rw [hX i]
    funext ω
    ring
  exact memLp_X_of_oneFactor μ hX' hT hE i

/-- Tau-equivalence plumbing, derived from the one-factor case: item
covariance splits into true plus error part. -/
private theorem cov_X_of_tauEquivalent {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ} {X : Fin k → Ω → ℝ}
    {T : Ω → ℝ} {c : Fin k → ℝ} {E : Fin k → Ω → ℝ}
    (hX : ∀ i, X i = fun ω => T ω + c i + E i ω)
    (hT : MemLp T 2 μ) (hE : ∀ i, MemLp (E i) 2 μ)
    (hTE : ∀ i, cov[T, E i; μ] = 0)
    (i j : Fin k) :
    cov[X i, X j; μ] = Var[T; μ] + cov[E i, E j; μ] := by
  have hX' : ∀ i, X i = fun ω => c i + 1 * T ω + E i ω := by
    intro i
    rw [hX i]
    funext ω
    ring
  have h := cov_X_of_oneFactor μ hX' hT hE hTE i j
  simpa using h

/-- Cronbach's coefficient alpha `α = k / (k - 1) * (1 - ∑ σ²_{Xᵢ} / σ²_X)`
(Cronbach 1951, as cited in Martinková and Hladká, Eq. 4.13).

The textbook ratio is defined only for `2 ≤ k` with positive total spread;
this function returns `0` outside that domain. Without the zero-covariance
model hypotheses, alpha is not identified with reliability: it can exceed
the spread ratio under correlated errors (see
`alpha_one_ratio_zero_of_correlated_errors`) and can even be negative (see
`alpha_neg_four_of_negative_cov`). -/
noncomputable def coefficientAlpha {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {k : ℕ} (X : Fin k → Ω → ℝ) : ℝ :=
  if 2 ≤ k ∧ 0 < Var[fun ω => ∑ i, X i ω; μ] then
    (k : ℝ) / ((k : ℝ) - 1) * (1 - (∑ i, Var[X i; μ]) / Var[fun ω => ∑ i, X i ω; μ])
  else 0

/-- Spread of the composite under tau-equivalence: the composite spread
splits into `k ^ 2 * Var[T]` plus the summed error spreads. -/
theorem variance_sum_of_tauEquivalent {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ} {X : Fin k → Ω → ℝ}
    {T : Ω → ℝ} {c : Fin k → ℝ} {E : Fin k → Ω → ℝ}
    (hX : ∀ i, X i = fun ω => T ω + c i + E i ω)
    (hT : MemLp T 2 μ) (hE : ∀ i, MemLp (E i) 2 μ)
    (hTE : ∀ i, cov[T, E i; μ] = 0)
    (hEE : ∀ i j, i ≠ j → cov[E i, E j; μ] = 0) :
    Var[fun ω => ∑ i, X i ω; μ] = (k : ℝ) ^ 2 * Var[T; μ] + ∑ i, Var[E i; μ] := by
  have hmem : ∀ i, MemLp (X i) 2 μ :=
    fun i => memLp_X_of_tauEquivalent μ hX hT hE i
  have hcov : ∀ i j, cov[X i, X j; μ]
      = Var[T; μ] + cov[E i, E j; μ] :=
    fun i j => cov_X_of_tauEquivalent μ hX hT hE hTE i j
  have hV : (∑ _ : Fin k, Var[T; μ]) = (k : ℝ) * Var[T; μ] := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcoll : ∀ i, (∑ j, cov[E i, E j; μ]) = Var[E i; μ] := by
    intro i
    rw [Finset.sum_eq_single i (fun j _ hji => hEE i j hji.symm)
      (fun h => absurd (Finset.mem_univ i) h)]
    exact covariance_self (hE i).aemeasurable
  have hkk : (∑ _ : Fin k, (k : ℝ) * Var[T; μ])
      = (k : ℝ) ^ 2 * Var[T; μ] := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [variance_fun_sum hmem]
  simp_rw [hcov, Finset.sum_add_distrib, hcoll, hV]
  rw [hkk]

/-- Under tau-equivalence, coefficient alpha equals the composite reliability
ratio `Var[k * T] / Var[∑ Xᵢ]`. -/
theorem coefficientAlpha_eq_variance_div_of_tauEquivalent {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ} {X : Fin k → Ω → ℝ}
    {T : Ω → ℝ} {c : Fin k → ℝ} {E : Fin k → Ω → ℝ}
    (hX : ∀ i, X i = fun ω => T ω + c i + E i ω)
    (hT : MemLp T 2 μ) (hE : ∀ i, MemLp (E i) 2 μ)
    (hTE : ∀ i, cov[T, E i; μ] = 0)
    (hEE : ∀ i j, i ≠ j → cov[E i, E j; μ] = 0)
    (hk : 2 ≤ k) (hpos : 0 < Var[fun ω => ∑ i, X i ω; μ]) :
    coefficientAlpha μ X = Var[fun ω => (k : ℝ) * T ω; μ] / Var[fun ω => ∑ i, X i ω; μ] := by
  have hV : (∑ _ : Fin k, Var[T; μ]) = (k : ℝ) * Var[T; μ] := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hitem : ∀ i, Var[X i; μ] = Var[T; μ] + Var[E i; μ] := by
    intro i
    have hXmem : MemLp (X i) 2 μ := memLp_X_of_tauEquivalent μ hX hT hE i
    have h := cov_X_of_tauEquivalent μ hX hT hE hTE i i
    rw [← covariance_self hXmem.aemeasurable, h,
      ← covariance_self (hE i).aemeasurable]
  have hsum : (∑ i, Var[X i; μ]) = (k : ℝ) * Var[T; μ] + ∑ i, Var[E i; μ] := by
    simp_rw [hitem, Finset.sum_add_distrib, hV]
  have htot : Var[fun ω => ∑ i, X i ω; μ]
      = (k : ℝ) ^ 2 * Var[T; μ] + ∑ i, Var[E i; μ] :=
    variance_sum_of_tauEquivalent μ hX hT hE hTE hEE
  have hnum : Var[fun ω => (k : ℝ) * T ω; μ] = (k : ℝ) ^ 2 * Var[T; μ] :=
    variance_const_mul _ _ _
  have hk0 : (k : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : k ≠ 0)
  have hk1 : (k : ℝ) - 1 ≠ 0 := by
    have h1 : (1 : ℝ) < (k : ℝ) := by
      exact_mod_cast (by omega : 1 < k)
    exact sub_ne_zero.mpr (ne_of_gt h1)
  have hD : (k : ℝ) ^ 2 * Var[T; μ] + ∑ i, Var[E i; μ] ≠ 0 := by
    rw [← htot]
    exact ne_of_gt hpos
  unfold coefficientAlpha
  rw [ite_eq_left ⟨hk, hpos⟩, hsum, htot, hnum]
  field_simp
  ring

/-- Under tau-equivalence with equal error spreads `σ2`, coefficient alpha
takes the Eq. 4.8 form `k ^ 2 * Var[T] / (k ^ 2 * Var[T] + k * σ2)`
(Eq. 4.8 of Martinková and Hladká). -/
theorem coefficientAlpha_eq_of_tauEquivalent_of_variance_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ} {X : Fin k → Ω → ℝ}
    {T : Ω → ℝ} {c : Fin k → ℝ} {E : Fin k → Ω → ℝ}
    (hX : ∀ i, X i = fun ω => T ω + c i + E i ω)
    (hT : MemLp T 2 μ) (hE : ∀ i, MemLp (E i) 2 μ)
    (hTE : ∀ i, cov[T, E i; μ] = 0)
    (hEE : ∀ i j, i ≠ j → cov[E i, E j; μ] = 0)
    (hk : 2 ≤ k) (hpos : 0 < Var[fun ω => ∑ i, X i ω; μ])
    (σ2 : ℝ) (hσ : ∀ i, Var[E i; μ] = σ2) :
    coefficientAlpha μ X
      = (k : ℝ) ^ 2 * Var[T; μ] / ((k : ℝ) ^ 2 * Var[T; μ] + k * σ2) := by
  have hmain := coefficientAlpha_eq_variance_div_of_tauEquivalent μ hX hT hE hTE hEE hk hpos
  have hS : (∑ i, Var[E i; μ]) = (k : ℝ) * σ2 := by
    simp_rw [hσ]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have htot := variance_sum_of_tauEquivalent μ hX hT hE hTE hEE
  have hnum : Var[fun ω => (k : ℝ) * T ω; μ] = (k : ℝ) ^ 2 * Var[T; μ] :=
    variance_const_mul _ _ _
  rw [hmain, htot, hnum, hS]

/-- McDonald's coefficient omega `ω₁ = (Σ λ)² φ / ((Σ λ)² φ + Σ Σ Θ)`
for a one-factor congeneric model (displayed formula from the semTools
`reliability` documentation, which cites Bollen 1980 and Raykov 2001).

`Θ` is meant to be a symmetric error covariance matrix; the double sum then
equals the displayed `∑ θᵢᵢ + 2 ∑_{i<j} θᵢⱼ` form.

The factor scale is not identified: rescaling loadings by `c ≠ 0` and the
factor spread to `φ / c ^ 2` leaves omega unchanged (see
`omega_invariant_under_rescaling`). -/
noncomputable def coefficientOmega {k : ℕ} (lam : Fin k → ℝ) (φ : ℝ)
    (Θ : Fin k → Fin k → ℝ) : ℝ :=
  (∑ i, lam i) ^ 2 * φ / ((∑ i, lam i) ^ 2 * φ + ∑ i, ∑ j, Θ i j)

/-- Spread of the composite under a one-factor congeneric model: the
composite spread splits into `(∑ lam) ^ 2 * Var[F]` plus the summed error
(co)spreads. -/
theorem variance_sum_of_oneFactor {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ} {X : Fin k → Ω → ℝ}
    {ν : Fin k → ℝ} {lam : Fin k → ℝ} {F : Ω → ℝ} {E : Fin k → Ω → ℝ}
    (hX : ∀ i, X i = fun ω => ν i + lam i * F ω + E i ω)
    (hF : MemLp F 2 μ) (hE : ∀ i, MemLp (E i) 2 μ)
    (hFE : ∀ i, cov[F, E i; μ] = 0) :
    Var[fun ω => ∑ i, X i ω; μ]
      = (∑ i, lam i) ^ 2 * Var[F; μ] + ∑ i, ∑ j, cov[E i, E j; μ] := by
  have hmem : ∀ i, MemLp (X i) 2 μ :=
    fun i => memLp_X_of_oneFactor μ hX hF hE i
  have hcov : ∀ i j, cov[X i, X j; μ]
      = lam i * lam j * Var[F; μ] + cov[E i, E j; μ] :=
    fun i j => cov_X_of_oneFactor μ hX hF hE hFE i j
  have hV : (∑ i, ∑ j, lam i * lam j * Var[F; μ])
      = (∑ i, lam i) ^ 2 * Var[F; μ] := by
    have e : ∀ i j, lam i * lam j * Var[F; μ] = lam i * (lam j * Var[F; μ]) := by
      intros
      ring
    simp_rw [e, ← Finset.sum_mul_sum, ← Finset.sum_mul]
    ring
  rw [variance_fun_sum hmem]
  simp_rw [hcov, Finset.sum_add_distrib, hV]

/-- Totalized algebraic form of the omega spread ratio, without the
positive-denominator domain hypothesis. -/
private theorem coefficientOmega_eq_variance_div_totalized {Ω : Type*}
    [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ} {X : Fin k → Ω → ℝ}
    {ν : Fin k → ℝ} {lam : Fin k → ℝ} {F : Ω → ℝ} {E : Fin k → Ω → ℝ}
    (hX : ∀ i, X i = fun ω => ν i + lam i * F ω + E i ω)
    (hF : MemLp F 2 μ) (hE : ∀ i, MemLp (E i) 2 μ)
    (hFE : ∀ i, cov[F, E i; μ] = 0)
    {φ : ℝ} {Θ : Fin k → Fin k → ℝ}
    (hφ : Var[F; μ] = φ) (hΘ : ∀ i j, cov[E i, E j; μ] = Θ i j) :
    coefficientOmega lam φ Θ
      = Var[fun ω => (∑ i, lam i) * F ω; μ]
        / Var[fun ω => ∑ i, X i ω; μ] := by
  have hC : Var[fun ω => (∑ i, lam i) * F ω; μ] = (∑ i, lam i) ^ 2 * φ := by
    rw [variance_const_mul, hφ]
  have hS : (∑ i, ∑ j, cov[E i, E j; μ]) = ∑ i, ∑ j, Θ i j :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hΘ i j))
  have hT : Var[fun ω => ∑ i, X i ω; μ]
      = (∑ i, lam i) ^ 2 * φ + ∑ i, ∑ j, Θ i j := by
    have h := variance_sum_of_oneFactor μ hX hF hE hFE
    rw [h, hφ, hS]
  unfold coefficientOmega
  rw [hC, hT]

/-- Under a one-factor congeneric model with specified factor spread `φ`
and error (co)spreads `Θ`, coefficient omega equals the composite
reliability ratio `Var[(Σ lam) * F] / Var[∑ Xᵢ]`.

This equality is a reliability only when the denominator is positive
(hypothesis `hpos`); see `omega_degenerate_zero_total_outside_domain` for
a model outside the domain. With correlated errors, alpha is not a lower
bound for omega (see `omega_zero_of_correlated_errors`). -/
theorem coefficientOmega_eq_variance_div_variance {Ω : Type*}
    [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ} {X : Fin k → Ω → ℝ}
    {ν : Fin k → ℝ} {lam : Fin k → ℝ} {F : Ω → ℝ} {E : Fin k → Ω → ℝ}
    (hX : ∀ i, X i = fun ω => ν i + lam i * F ω + E i ω)
    (hF : MemLp F 2 μ) (hE : ∀ i, MemLp (E i) 2 μ)
    (hFE : ∀ i, cov[F, E i; μ] = 0)
    {φ : ℝ} {Θ : Fin k → Fin k → ℝ}
    (hφ : Var[F; μ] = φ) (hΘ : ∀ i j, cov[E i, E j; μ] = Θ i j)
    (hpos : 0 < Var[fun ω => ∑ i, X i ω; μ]) :
    coefficientOmega lam φ Θ
      = Var[fun ω => (∑ i, lam i) * F ω; μ]
        / Var[fun ω => ∑ i, X i ω; μ] := by
  have _hne : Var[fun ω => ∑ i, X i ω; μ] ≠ 0 := ne_of_gt hpos
  exact coefficientOmega_eq_variance_div_totalized μ hX hF hE hFE hφ hΘ

/-- Under uncorrelated errors, coefficient omega takes the diagonal form
`(Σ lam) ^ 2 * φ / ((Σ lam) ^ 2 * φ + ∑ Θᵢᵢ)`. This is pure algebra with no
model: the `[0, 1]` range claim belongs to the full one-factor model (see
`coefficientOmega_mem_Icc`), not to this form. -/
theorem coefficientOmega_eq_of_diagonal {k : ℕ} (lam : Fin k → ℝ) (φ : ℝ)
    (Θ : Fin k → Fin k → ℝ) (hΘ : ∀ i j, i ≠ j → Θ i j = 0) :
    coefficientOmega lam φ Θ
      = (∑ i, lam i) ^ 2 * φ / ((∑ i, lam i) ^ 2 * φ + ∑ i, Θ i i) := by
  have hS : (∑ i, ∑ j, Θ i j) = ∑ i, Θ i i :=
    Finset.sum_congr rfl (fun i _ => Finset.sum_eq_single i
      (fun j _ hji => hΘ i j hji.symm) (fun h => absurd (Finset.mem_univ i) h))
  unfold coefficientOmega
  rw [hS]

/-- Under a one-factor congeneric model with specified factor spread `φ`
and error (co)spreads `Θ`, and positive total spread, coefficient omega
lies in `[0, 1]`. -/
theorem coefficientOmega_mem_Icc {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k : ℕ} {X : Fin k → Ω → ℝ}
    {ν : Fin k → ℝ} {lam : Fin k → ℝ} {F : Ω → ℝ} {E : Fin k → Ω → ℝ}
    (hX : ∀ i, X i = fun ω => ν i + lam i * F ω + E i ω)
    (hF : MemLp F 2 μ) (hE : ∀ i, MemLp (E i) 2 μ)
    (hFE : ∀ i, cov[F, E i; μ] = 0)
    {φ : ℝ} {Θ : Fin k → Fin k → ℝ}
    (hφ : Var[F; μ] = φ) (hΘ : ∀ i j, cov[E i, E j; μ] = Θ i j)
    (hpos : 0 < Var[fun ω => ∑ i, X i ω; μ]) :
    coefficientOmega lam φ Θ ∈ Set.Icc 0 1 := by
  have hEsum : MemLp (fun ω => ∑ i, E i ω) 2 μ :=
    memLp_finsetSum _ (fun i _ => hE i)
  have hcom : MemLp (fun ω => (∑ i, lam i) * F ω) 2 μ :=
    hF.const_mul _
  have hrem : MemLp ((fun _ => ∑ i, ν i) + (fun ω => ∑ i, E i ω)) 2 μ :=
    (memLp_const _).add hEsum
  have hsplit : (fun ω => ∑ i, X i ω)
      = (fun ω => (∑ i, lam i) * F ω)
        + ((fun _ => ∑ i, ν i) + (fun ω => ∑ i, E i ω)) := by
    funext ω
    simp only [Pi.add_apply]
    simp_rw [hX, Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  have hcov : cov[fun ω => (∑ i, lam i) * F ω,
      (fun _ => ∑ i, ν i) + (fun ω => ∑ i, E i ω); μ] = 0 := by
    rw [covariance_add_right hcom (memLp_const (∑ i, ν i)) hEsum,
      covariance_const_right, zero_add,
      covariance_fun_sum_right hE hcom]
    simp_rw [covariance_const_mul_left, hFE, mul_zero, Finset.sum_const_zero]
  have hVT : Var[fun ω => ∑ i, X i ω; μ]
      = Var[fun ω => (∑ i, lam i) * F ω; μ]
        + Var[(fun _ => ∑ i, ν i) + (fun ω => ∑ i, E i ω); μ] := by
    rw [hsplit]
    exact variance_add_of_cov_eq_zero μ hcom hrem hcov
  have hCnn : 0 ≤ Var[fun ω => (∑ i, lam i) * F ω; μ] :=
    variance_nonneg _ _
  have hle : Var[fun ω => (∑ i, lam i) * F ω; μ]
      ≤ Var[fun ω => ∑ i, X i ω; μ] := by
    rw [hVT]
    exact le_add_of_nonneg_right (variance_nonneg _ _)
  have heq := coefficientOmega_eq_variance_div_variance μ hX hF hE hFE hφ hΘ hpos
  rw [heq, Set.mem_Icc]
  exact ⟨div_nonneg hCnn (le_of_lt hpos), (div_le_one hpos).mpr hle⟩

end MathlibExt.Probability.Statistics.Measurement
