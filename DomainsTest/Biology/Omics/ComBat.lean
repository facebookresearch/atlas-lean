/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Omics.ComBat
import MathlibExt.Probability.FiniteProbability
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Tests for the ComBat empirical Bayes batch adjustment.

* An unbalanced design with one covariate, batches of `3` and `2` samples, is identifiable, and
  the standardization recovers the overall level `2`, the covariate effect `3` and the batch
  effects `2, -3` of noise-free data, which satisfy the constraint `3 * 2 + 2 * (-3) = 0`.
* Two genes in two batches of two samples, with no covariates (`Y₂`):

  | gene | batch `0` | batch `1` | `α̂` | `γ̃` | `σ̂` |
  |---|---|---|---|---|---|
  | `0` | `2, 0` | `0, -2` | `0` | `1, -1` | `1` |
  | `1` | `22, 8` | `6, 4` | `10` | `5, -5` | `5` |

  The least-squares coefficients are the batch means. The standardized data are `2, 0, 0, -2` and
  `12/5, -2/5, -4/5, -6/5` (`Z₂`). Both genes have the standardized batch means `1` and `-1`, so
  `τ̄² = 0` in each batch and the location estimate is the batch-wide mean, `γ* = γ̄`. The
  gene-wise variances are `2, 98/25` in batch `0` and `2, 2/25` in batch `1`, with positive
  variance `1152/625` over the genes, so `empiricalBayes_fixedPoint` applies; in batch `0`,
  `V = 74/25`, `λ̄ = 1945/288` and `θ̄ = 61309/3600`. Since `τ̄² = 0`, the iteration is constant
  after its first step, at `δ*² = (θ̄ + δ̂'² / 2) / λ̄`: `129818/48625` and `27346/9725` for the
  two genes in batch `0`, and `2434/3725` for gene `1` in batch `1`. These values are computed
  from the definition: gene `0` in sample `0` is adjusted to its residual `1` divided by
  `√(129818/48625)`, gene `1` in sample `0` to `7 / √(27346/9725) + 10` and in sample `3` to
  `-1 / √(2434/3725) + 10`.
* `Z₂` is the standardized data of `Y₂`, so `adjust_eq_of_standardized` expresses the adjusted data
  of `Y₂` through `Z₂` and the estimates of `empiricalBayes_fixedPoint` for `Z₂`.
* The same residuals without the batch mean shifts (`Y₃`) give the same adjusted value of gene `0`
  in sample `0`: the shifts are removed.
* Rescaling gene `1` by `y ↦ 2 y + 3` leaves gene `0` unchanged, and rescaling gene `0` rescales
  its adjusted value in the same way. -/

open Filter Topology Matrix
open scoped Finset
open MathlibExt.Probability.Statistics.LinearModel
open Domains.Biology.Omics.ComBat

namespace DomainsTest.Biology.Omics.ComBat

/-! ### An unbalanced design with one covariate -/

/-- Three samples in batch `0` and two in batch `1`. -/
def batch₁ : Fin 5 → Fin 2 := ![0, 0, 0, 1, 1]

/-- One covariate, a treatment indicator. -/
def x₁ : Fin 5 → Unit → ℝ := fun s _ => ![0, 1, 0, 1, 1] s

/-- The design of batch indicators and the treatment indicator is identifiable. -/
theorem ident₁ : ∀ (b : Fin 2 → ℝ) (c : Unit → ℝ),
    (∀ s, b (batch₁ s) + ∑ k, x₁ s k * c k = 0) → b = 0 ∧ c = 0 := by
  intro b c h
  have h0 := h 0
  have h1 := h 1
  have h3 := h 3
  simp [batch₁, x₁] at h0 h1 h3
  have hc : c () = 0 := by linarith
  refine ⟨funext fun i => ?_, funext fun k => by simpa using hc⟩
  fin_cases i
  · simpa using h0
  · simp only [Fin.mk_one, Pi.zero_apply]
    linarith

/-- Noise-free data `2 + 3 x + γ (batch s)` with batch effects `γ = (2, -3)`, which satisfy
`3 * 2 + 2 * (-3) = 0`. -/
noncomputable def y₁ : Fin 5 → ℝ := ![4, 7, 4, 2, 2]

/-- The standardization recovers `α̂ = 2`, `β̂ = 3` and `γ̃ = (2, -3)` from the noise-free data. -/
theorem standardization_exact :
    let B : Fin 2 ⊕ Unit → ℝ :=
      olsEstimator (Matrix.of fun s => Sum.elim (fun i => if batch₁ s = i then 1 else 0) (x₁ s)) y₁
    ∑ i, (#{s | batch₁ s = i} : ℝ) / Fintype.card (Fin 5) * B (.inl i) = 2 ∧ B (.inr ()) = 3 ∧
      B (.inl 0) - 2 = 2 ∧ B (.inl 1) - 2 = -3 := by
  intro B
  obtain ⟨-, -, huniq⟩ := leastSquares_standardization ident₁ y₁
  have hn0 : #{s | batch₁ s = 0} = 3 := by decide
  have hn1 : #{s | batch₁ s = 1} = 2 := by decide
  have hcon : ∑ i, (#{s | batch₁ s = i} : ℝ) * ![2, -3] i = 0 := by
    simp [Fin.sum_univ_two, hn0, hn1]
    norm_num
  have hfit : ∑ s, (y₁ s - 2 - ∑ k, x₁ s k * (fun _ => (3 : ℝ)) k - ![2, -3] (batch₁ s)) ^ 2 =
      0 := by
    simp [Fin.sum_univ_five, y₁, x₁, batch₁]
    norm_num
  obtain ⟨hα, hβ, hγ⟩ := huniq 2 (fun _ => 3) ![2, -3] hcon
    (hfit.le.trans (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hγ0 := congr_fun hγ 0
  have hγ1 := congr_fun hγ 1
  rw [← hα] at hγ0 hγ1
  exact ⟨hα.symm, (congr_fun hβ ()).symm, by simpa using hγ0.symm, by simpa using hγ1.symm⟩

/-! ### Two genes in two batches, with no covariates -/

/-- Two samples in each of two batches. -/
def batch₂ : Fin 4 → Fin 2 := ![0, 0, 1, 1]

/-- No covariates. -/
def x₂ : Fin 4 → Fin 0 → ℝ := fun _ k => k.elim0

/-- The design of batch indicators is identifiable. -/
theorem ident₂ : ∀ (b : Fin 2 → ℝ) (c : Fin 0 → ℝ),
    (∀ s, b (batch₂ s) + ∑ k, x₂ s k * c k = 0) → b = 0 ∧ c = 0 := by
  intro b c h
  have h0 := h 0
  have h2 := h 2
  simp [batch₂] at h0 h2
  refine ⟨funext fun i => ?_, funext fun k => k.elim0⟩
  fin_cases i
  · simpa using h0
  · simpa using h2

/-- Expression values with batch mean shifts: the batch means of gene `0` are `1` and `-1`, and
those of gene `1` are `15` and `5`. -/
noncomputable def Y₂ : Fin 2 → Fin 4 → ℝ := ![![2, 0, 0, -2], ![22, 8, 6, 4]]

/-- The same residuals without batch mean shifts. -/
noncomputable def Y₃ : Fin 2 → Fin 4 → ℝ := ![![1, -1, 1, -1], ![17, 3, 11, 9]]

/-- The standardized data of `Y₂`. -/
noncomputable def Z₂ : Fin 2 → Fin 4 → ℝ := ![![2, 0, 0, -2], ![12 / 5, -2 / 5, -4 / 5, -6 / 5]]

/-- An orbit that reaches a fixed point `c` in one step has limit `c`. -/
theorem limUnder_iterate_of_fixed {f : ℝ → ℝ} {d c : ℝ} (h₁ : f d = c) (h₂ : f c = c) :
    limUnder atTop (fun k => f^[k] d) = c := by
  refine Tendsto.limUnder_eq (tendsto_atTop_of_eventually_const (i₀ := 1) fun k hk => ?_)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
  induction j with
  | zero => simpa using h₁
  | succ j ih => rw [Function.iterate_succ_apply', ih (by omega), h₂]

/-- The Gram matrix of the batch indicators is invertible. -/
theorem isUnit₂ :
    IsUnit ((Matrix.of fun s => Sum.elim (fun i => if batch₂ s = i then (1 : ℝ) else 0) (x₂ s))ᵀ *
      Matrix.of fun s => Sum.elim (fun i => if batch₂ s = i then (1 : ℝ) else 0) (x₂ s)) := by
  refine (MathlibExt.Probability.FiniteProbability.isUnit_transpose_mul_self_iff _).mpr
    (Matrix.mulVec_injective_iff.mp fun v w hvw => ?_)
  have h0 := congr_fun hvw 0
  have h2 := congr_fun hvw 2
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, batch₂] at h0 h2
  funext j
  rcases j with j | j
  · fin_cases j
    · exact h0
    · exact h2
  · exact j.elim0

/-- The least-squares coefficients are the batch means. -/
theorem coef₂ (g : Fin 2) : olsEstimator (Matrix.of fun s =>
    Sum.elim (fun i => if batch₂ s = i then (1 : ℝ) else 0) (x₂ s)) (Y₂ g) =
      Sum.elim (![![1, -1], ![15, 5]] g) fun k : Fin 0 => k.elim0 := by
  refine ((MathlibExt.Probability.FiniteProbability.eq_olsEstimator_iff isUnit₂ _ _).mp ?_).symm
  funext j
  rcases j with j | j
  · fin_cases g <;> fin_cases j <;>
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_four,
        Function.swap, batch₂, Y₂] <;> norm_num
  · exact j.elim0

/-- The least-squares coefficients are the batch means. -/
theorem coef₃ (g : Fin 2) : olsEstimator (Matrix.of fun s =>
    Sum.elim (fun i => if batch₂ s = i then (1 : ℝ) else 0) (x₂ s)) (Y₃ g) =
      Sum.elim (![![0, 0], ![10, 10]] g) fun k : Fin 0 => k.elim0 := by
  refine ((MathlibExt.Probability.FiniteProbability.eq_olsEstimator_iff isUnit₂ _ _).mp ?_).symm
  funext j
  rcases j with j | j
  · fin_cases g <;> fin_cases j <;>
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_four,
        Function.swap, batch₂, Y₃] <;> norm_num
  · exact j.elim0

/-- The batches of the four samples. -/
theorem batch₂_apply : batch₂ 0 = 0 ∧ batch₂ 1 = 0 ∧ batch₂ 2 = 1 ∧ batch₂ 3 = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The samples of each batch. -/
theorem filter_batch₂ : (Finset.univ.filter fun s : Fin 4 => batch₂ s = 0) = {0, 1} ∧
    (Finset.univ.filter fun s : Fin 4 => batch₂ s = 1) = {2, 3} := by
  decide

/-- `√4 = 2`. -/
theorem sqrt_four : √(4 : ℝ) = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `√25 = 5`. -/
theorem sqrt_twentyFive : √(25 : ℝ) = 5 := by
  rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- Without batch mean shifts: gene `0` in sample `0` has the residual `1`, which the empirical
Bayes scale `δ*² = 129818/48625` divides. -/
theorem adjust_Y₃_zero_zero : adjust batch₂ x₂ Y₃ 0 0 = 1 / √(129818 / 48625) := by
  simp only [adjust, coef₃]
  simp only [batch₂_apply, filter_batch₂, Fin.sum_univ_two, Fin.sum_univ_four, Fin.sum_univ_zero]
  rw [limUnder_iterate_of_fixed (c := 129818 / 48625)]
  · norm_num [Y₃, sqrt_four, sqrt_twentyFive]
  all_goals norm_num [Y₃, sqrt_four, sqrt_twentyFive]

/-- With batch mean shifts the adjusted value is the same: the shift `γ̃ = 1` of batch `0` is
removed, as `γ* = γ̄ = 1`. -/
theorem adjust_Y₂_zero_zero : adjust batch₂ x₂ Y₂ 0 0 = 1 / √(129818 / 48625) := by
  simp only [adjust, coef₂]
  simp only [batch₂_apply, filter_batch₂, Fin.sum_univ_two, Fin.sum_univ_four, Fin.sum_univ_zero]
  rw [limUnder_iterate_of_fixed (c := 129818 / 48625)]
  · norm_num [Y₂, sqrt_four, sqrt_twentyFive]
  all_goals norm_num [Y₂, sqrt_four, sqrt_twentyFive]

/-- Gene `1` in sample `0`: `α̂ = 10`, `σ̂ = 5`, `Z = 12/5`, `γ* = 1` and
`δ*² = 27346/9725`. -/
theorem adjust_Y₂_one_zero : adjust batch₂ x₂ Y₂ 1 0 = 7 / √(27346 / 9725) + 10 := by
  simp only [adjust, coef₂]
  simp only [batch₂_apply, filter_batch₂, Fin.sum_univ_two, Fin.sum_univ_four, Fin.sum_univ_zero]
  rw [limUnder_iterate_of_fixed (c := 27346 / 9725)]
  · norm_num [Y₂, sqrt_four, sqrt_twentyFive]
  all_goals norm_num [Y₂, sqrt_four, sqrt_twentyFive]

/-- Gene `1` in sample `3`, in batch `1`: `Z = -6/5`, `γ* = γ̄ = -1` and
`δ*² = 2434/3725`. -/
theorem adjust_Y₂_one_three : adjust batch₂ x₂ Y₂ 1 3 = -1 / √(2434 / 3725) + 10 := by
  simp only [adjust, coef₂]
  simp only [batch₂_apply, filter_batch₂, Fin.sum_univ_two, Fin.sum_univ_four, Fin.sum_univ_zero]
  rw [limUnder_iterate_of_fixed (c := 2434 / 3725)]
  · norm_num [Y₂, sqrt_four, sqrt_twentyFive]
    rw [neg_div, one_div_div]
  all_goals norm_num [Y₂, sqrt_four, sqrt_twentyFive]

/-- The gene-wise variances `2` and `98/25` of batch `0` have positive variance `1152/625` over
the genes, so `empiricalBayes_fixedPoint` applies to the standardized data `Z₂`. -/
example (g : Fin 2) := empiricalBayes_fixedPoint batch₂ Z₂ 0 g
  (by norm_num [Z₂, batch₂_apply, filter_batch₂, Fin.sum_univ_two])

/-- `Z₂` is the standardized data of `Y₂`, so `adjust_eq_of_standardized` writes the adjusted data
of `Y₂` through `Z₂` and the estimates of `empiricalBayes_fixedPoint` for `Z₂`. -/
example (g : Fin 2) (s : Fin 4) := adjust_eq_of_standardized batch₂ x₂ Y₂ Z₂ g s (by
  intro h t
  simp only [coef₂]
  fin_cases h <;> fin_cases t <;>
    norm_num [Z₂, Y₂, batch₂_apply, filter_batch₂, Fin.sum_univ_two, Fin.sum_univ_four,
      sqrt_four, sqrt_twentyFive])

/-- Rescaling gene `1` by `y ↦ 2 y + 3` leaves the adjusted data of gene `0` unchanged. -/
theorem adjust_update_one : adjust batch₂ x₂ (Function.update Y₂ 1 fun s => 2 * Y₂ 1 s + 3) 0 0 =
    1 / √(129818 / 48625) := by
  rw [adjust_update_affine ident₂ Y₂ 1 (by norm_num) 3, Function.update_of_ne (by decide),
    adjust_Y₂_zero_zero]

/-- Rescaling gene `0` by `y ↦ 2 y + 3` rescales its adjusted data in the same way. -/
theorem adjust_update_zero : adjust batch₂ x₂ (Function.update Y₂ 0 fun s => 2 * Y₂ 0 s + 3) 0 0 =
    2 * (1 / √(129818 / 48625)) + 3 := by
  rw [adjust_update_affine ident₂ Y₂ 0 (by norm_num) 3, Function.update_self, adjust_Y₂_zero_zero]

end DomainsTest.Biology.Omics.ComBat
