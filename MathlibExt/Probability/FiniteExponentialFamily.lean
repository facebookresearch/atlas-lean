/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import MathlibExt.InformationTheory.LogSum

/-!
# Exponential families on a finite space: the log-partition function and its variational form

An exponential family on a finite set `X` with sufficient statistic `φ : X → E` (a real inner
product space) is the family of distributions `p_θ(x) = exp (⟪φ x, θ⟫ - A θ)`, `θ ∈ E`, where the
**log-partition (cumulant) function** is `A θ = log ∑ₓ exp ⟪φ x, θ⟫`: equation (3.40) of
M. J. Wainwright and M. I. Jordan, *Graphical models, exponential families, and variational
inference*, Found. Trends Mach. Learn. 1 (2008), with `ν` the counting measure on `X`. On a finite
space the family is regular with domain `Ω = E`.

## Main results

* `hasGradientAt_logPartition`: `∇A(θ) = E_θ[φ(X)]`, the mean parameter (Proposition 3.1(a),
  eq. (3.41a)).
* `sum_mul_inner_sub_log_le` and `sum_density_mul_inner_sub_log`: the Gibbs variational
  principle `A θ = max_q (∑ₓ q x ⟪φ x, θ⟫ + H(q))` over distributions `q` on `X`, attained at
  `q = p_θ`; this is the finite form of the variational representation (3.45) of Theorem 3.4,
  before the maximization over `q` with a given mean parameter.
* `convexOn_logPartition`: `A` is convex (Proposition 3.1(b)), here deduced from the
  variational principle as a supremum of affine functions of `θ`.
-/

@[expose] public section

open Finset Real

namespace MathlibExt.Probability.FiniteExponentialFamily

variable {X : Type*} [Fintype X] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Partition function of a finite exponential family.** `Z(θ) = ∑ₓ exp ⟪φ x, θ⟫`. -/
noncomputable def partitionSum (φ : X → E) (θ : E) : ℝ := ∑ x, exp (inner ℝ (φ x) θ)

/-- **Log-partition (cumulant) function of a finite exponential family.**
`A(θ) = log ∑ₓ exp ⟪φ x, θ⟫`: equation (3.40) of Wainwright and Jordan, *Graphical models,
exponential families, and variational inference* (2008), with the counting measure on the finite
set `X`. -/
noncomputable def logPartition (φ : X → E) (θ : E) : ℝ := log (partitionSum φ θ)

/-- **Density of a finite exponential family.** `p_θ(x) = exp ⟪φ x, θ⟫ / Z(θ)
= exp (⟪φ x, θ⟫ - A(θ))` (Wainwright and Jordan (2008), Section 3.2). -/
noncomputable def density (φ : X → E) (θ : E) (x : X) : ℝ :=
  exp (inner ℝ (φ x) θ) / partitionSum φ θ

/-- **Mean parameter of a finite exponential family.** `μ(θ) = E_θ[φ(X)] = ∑ₓ p_θ(x) φ(x)`
(Wainwright and Jordan (2008), Section 3.4). -/
noncomputable def meanParameter (φ : X → E) (θ : E) : E := ∑ x, density φ θ x • φ x

/-- **The partition function is positive** on a nonempty finite set: `Z(θ) > 0`. -/
theorem partitionSum_pos [Nonempty X] (φ : X → E) (θ : E) : 0 < partitionSum φ θ :=
  sum_pos (fun _ _ => exp_pos _) univ_nonempty

/-- **The density is a probability distribution.** `p_θ(x) > 0` and `∑ₓ p_θ(x) = 1`. -/
theorem density_pos_and_sum_eq_one [Nonempty X] (φ : X → E) (θ : E) :
    (∀ x, 0 < density φ θ x) ∧ ∑ x, density φ θ x = 1 :=
  ⟨fun x => div_pos (exp_pos _) (partitionSum_pos φ θ), by
    simp only [density]; rw [← sum_div]; exact div_self (partitionSum_pos φ θ).ne'⟩

/-- **The gradient of the log-partition function is the mean parameter.** For a finite
exponential family on a nonempty set, `∇A(θ) = E_θ[φ(X)] = ∑ₓ p_θ(x) φ(x)` at every `θ`.

Source: M. J. Wainwright and M. I. Jordan, *Graphical models, exponential families, and
variational inference*, Found. Trends Mach. Learn. 1 (2008), Proposition 3.1(a), first-derivative
part, eq. (3.41a), with the counting measure. -/
theorem hasGradientAt_logPartition [Nonempty X] [CompleteSpace E] (φ : X → E) (θ : E) :
    HasGradientAt (logPartition φ) (meanParameter φ θ) θ := by
  have hS : HasFDerivAt (partitionSum φ)
      (∑ x, exp (inner ℝ (φ x) θ) • innerSL ℝ (φ x)) θ := by
    have := HasFDerivAt.sum (u := univ) (A := fun x θ => exp (inner ℝ (φ x) θ))
      (fun x _ => ((innerSL ℝ (φ x)).hasFDerivAt (x := θ)).exp)
    have hfun : partitionSum φ = ∑ i, fun θ => exp (inner ℝ (φ i) θ) := by
      ext θ; simp [partitionSum, Finset.sum_apply]
    rw [hfun]; simpa using this
  have hL := hS.log (partitionSum_pos φ θ).ne'
  rw [hasGradientAt_iff_hasFDerivAt]
  refine HasFDerivAt.congr_fderiv (f := logPartition φ) hL ?_
  ext y
  simp only [InnerProductSpace.toDual_apply_apply, meanParameter, density, sum_inner,
    real_inner_smul_left, smul_apply, _root_.sum_apply,
    coe_innerSL_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- **Gibbs variational principle, upper bound.** For every probability distribution `q` on `X`
(`q ≥ 0`, `∑ q = 1`), `∑ₓ q x (⟪φ x, θ⟫ - log q x) ≤ A(θ)`: the expected statistic paired with
`θ` plus the Shannon entropy of `q` never exceeds the log-partition function.

Gibbs variational principle (finite form); cf. M. J. Wainwright and M. I. Jordan (2008),
Theorem 3.4(b), the representation (3.45) `A(θ) = sup_μ {⟨θ, μ⟩ - A*(μ)}` over mean parameters,
which follows from this form via Theorem 3.4(a) (not formalized here). It is the special case of
`MathlibExt.InformationTheory.DonskerVaradhan.isGreatest_integral_sub_klDiv` with `ν` uniform on
`X` and `f = ⟪φ ·, θ⟫`, since `log ∫ e^f dν = A(θ) - log |X|` and
`KL(q ‖ ν) = log |X| - H(q)`. The proof is the log-sum inequality. -/
theorem sum_mul_inner_sub_log_le (φ : X → E) (θ : E) {q : X → ℝ} (hq0 : ∀ x, 0 ≤ q x)
    (hq1 : ∑ x, q x = 1) :
    ∑ x, q x * (inner ℝ (φ x) θ - log (q x)) ≤ logPartition φ θ := by
  have h := Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div univ q
    (fun x => exp (inner ℝ (φ x) θ)) (fun x _ => hq0 x) (fun x _ => exp_pos _)
  rw [hq1, one_mul, one_div, log_inv] at h
  have hterm : ∀ x, q x * log (q x / exp (inner ℝ (φ x) θ)) =
      -(q x * (inner ℝ (φ x) θ - log (q x))) := by
    intro x
    rcases (hq0 x).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · rw [log_div hpos.ne' (exp_pos _).ne', log_exp]; ring
  simp only [hterm, Finset.sum_neg_distrib] at h
  rw [logPartition, partitionSum]
  linarith

/-- **Gibbs variational principle, attainment.** At the exponential-family density itself,
`∑ₓ p_θ(x) (⟪φ x, θ⟫ - log p_θ(x)) = A(θ)`, so `A(θ) = ⟪E_θ[φ], θ⟫ + H(p_θ)` and the supremum of
`sum_mul_inner_sub_log_le` is attained at `q = p_θ`.

Gibbs variational principle, attainment (finite form); cf. M. J. Wainwright and M. I. Jordan
(2008), Theorem 3.4(c) (the supremum in (3.45) is attained at the moment-matching mean parameter
`μ = E_θ[φ(X)]`). It is the attainment part of
`MathlibExt.InformationTheory.DonskerVaradhan.isGreatest_integral_sub_klDiv` (the tilted measure)
for `ν` uniform on `X`. -/
theorem sum_density_mul_inner_sub_log [Nonempty X] (φ : X → E) (θ : E) :
    ∑ x, density φ θ x * (inner ℝ (φ x) θ - log (density φ θ x)) = logPartition φ θ := by
  have hZ := partitionSum_pos φ θ
  have hterm : ∀ x, density φ θ x * (inner ℝ (φ x) θ - log (density φ θ x)) =
      density φ θ x * logPartition φ θ := by
    intro x
    rw [density, log_div (exp_pos _).ne' hZ.ne', log_exp, logPartition]
    ring
  rw [Finset.sum_congr rfl fun x _ => hterm x, ← Finset.sum_mul,
    (density_pos_and_sum_eq_one φ θ).2, one_mul]

/-- **The log-partition function is convex.** For a finite exponential family on a nonempty set,
`θ ↦ A(θ)` is convex on `E`.

Source: M. J. Wainwright and M. I. Jordan (2008), Proposition 3.1(b). Their proof uses the
Hessian (the covariance of `φ(X)`); here convexity follows from the Gibbs variational principle,
`A` being a pointwise maximum of affine functions of `θ`. -/
theorem convexOn_logPartition [Nonempty X] (φ : X → E) :
    ConvexOn ℝ Set.univ (logPartition φ) := by
  refine ⟨convex_univ, fun θ₁ _ θ₂ _ a b ha hb hab => ?_⟩
  set q := density φ (a • θ₁ + b • θ₂)
  obtain ⟨hqpos, hq1⟩ := density_pos_and_sum_eq_one φ (a • θ₁ + b • θ₂)
  have h1 := sum_mul_inner_sub_log_le φ θ₁ (fun x => (hqpos x).le) hq1
  have h2 := sum_mul_inner_sub_log_le φ θ₂ (fun x => (hqpos x).le) hq1
  have heq := sum_density_mul_inner_sub_log φ (a • θ₁ + b • θ₂)
  have hsplit : ∑ x, q x * (inner ℝ (φ x) (a • θ₁ + b • θ₂) - log (q x)) =
      a * ∑ x, q x * (inner ℝ (φ x) θ₁ - log (q x)) +
        b * ∑ x, q x * (inner ℝ (φ x) θ₂ - log (q x)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    linear_combination (q x * log (q x)) * hab
  simp only [smul_eq_mul]
  rw [← heq, hsplit]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

end MathlibExt.Probability.FiniteExponentialFamily
