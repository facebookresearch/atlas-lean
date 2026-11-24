/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# ℓ₂-error bounds for the Lasso under a restricted eigenvalue condition

Sparse linear regression observes `y = X θ* + w` with a design matrix
`X : Matrix (Fin n) ι ℝ`, an unknown parameter `θ* : ι → ℝ` supported on a set `S` of
`s = |S|` coordinates, and a noise vector `w`. Following Hastie, Tibshirani and Wainwright,
*Statistical Learning with Sparsity: The Lasso and Generalizations* (CRC Press, 2015), §11.2, and
Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint* (Cambridge University
Press, 2019), §7.3:

* `cone S α` is the cone `C(S; α) = {Δ | ‖Δ_{Sᶜ}‖₁ ≤ α ‖Δ_S‖₁}` (Hastie et al. 2015, eq. (11.13)).
* `RestrictedEigenvalue X S κ α` is the restricted eigenvalue condition with constant `κ > 0` over
  `C(S; α)`: `(1/n) ‖X Δ‖₂² ≥ κ ‖Δ‖₂²` for every `Δ ∈ C(S; α)` (Hastie et al. 2015, eq. (11.10);
  Wainwright 2019, §7.3.1).
* `lassoObjective X y lam θ = (1/(2n)) ‖y - X θ‖₂² + lam ‖θ‖₁` is the regularized (Lagrangian)
  Lasso objective (Hastie et al. 2015, eq. (11.3)).

## Main results

* `lasso_basic_inequality`: the modified basic inequality. If `θ̂` has Lasso objective at most
  that of `θ*` and `lam ≥ 2 ‖Xᵀ w / n‖_∞` with `lam > 0`, then the error `θ̂ - θ*` lies in
  `C(S; 3)` (Hastie et al. 2015, Lemma 11.1) and `(1/n) ‖X Δ‖₂² ≤ 3 lam ‖Δ_S‖₁`.
* `lasso_l2_error_le`: under the restricted eigenvalue condition over `C(S; 3)`, any minimiser of
  the Lagrangian Lasso satisfies `‖θ̂ - θ*‖₂ ≤ (3 / κ) √s lam` (Hastie et al. 2015,
  Theorem 11.1(b); Wainwright 2019, §7.3.2).
* `constrainedLasso_l2_error_le`: under the restricted eigenvalue condition over `C(S; 1)`, any
  minimiser of the constrained Lasso `min {(1/(2n)) ‖y - X θ‖₂² | ‖θ‖₁ ≤ ‖θ*‖₁}` satisfies
  `‖θ̂ - θ*‖₂ ≤ (4 / κ) √s ‖Xᵀ w / n‖_∞` (Hastie et al. 2015, Theorem 11.1(a), whose proof only
  uses the cone `C(S; 1) ⊆ C(S; 3)`; Wainwright 2019, §7.3.2).
* `lasso_prediction_error_le_slow` and `lasso_prediction_error_le_fast`: the slow rate
  `(1/n) ‖X (θ̂ - θ*)‖₂² ≤ 12 R₁ lam` when `‖θ*‖₁ ≤ R₁`, with no condition on `X`, and the fast
  rate `≤ (9 / κ) |S| lam²` under the restricted eigenvalue condition over `C(S; 3)` (Hastie et
  al. 2015, Theorem 11.2). `lasso_prediction_error_le_three` sharpens the slow rate to
  `3 lam ‖θ*‖₁`, by a variant of the source's argument proved here.

The statements are deterministic: they hold for every realisation of the noise. Norms are written
as explicit sums, `‖Δ‖₂ = √(∑ j, Δ j ^ 2)` and `‖Δ‖₁ = ∑ j, |Δ j|`, and the sup norm
`‖Xᵀ w / n‖_∞` is replaced by any upper bound `ν` on `|(Xᵀ w) j| / n` over all coordinates `j`,
which is equivalent (take `ν` the maximum).
-/

open Finset Matrix

namespace MathlibExt.Probability.Statistics.LassoRestrictedEigenvalue

@[expose] public section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- The cone `C(S; α) = {Δ | ‖Δ_{Sᶜ}‖₁ ≤ α ‖Δ_S‖₁}` of vectors whose `ℓ₁` mass off a support set
`S` is at most `α` times their mass on `S` (Hastie, Tibshirani and Wainwright, *Statistical
Learning with Sparsity*, 2015, eq. (11.13)). -/
def cone (S : Finset ι) (α : ℝ) : Set (ι → ℝ) :=
  {Δ | ∑ j ∈ Sᶜ, |Δ j| ≤ α * ∑ j ∈ S, |Δ j|}

/-- The restricted eigenvalue condition with parameters `(κ, α)` over `S` for a design matrix
`X` with `n` rows: `κ > 0` and `(1/n) ‖X Δ‖₂² ≥ κ ‖Δ‖₂²` for every `Δ` in the cone `C(S; α)`
(Hastie, Tibshirani and Wainwright, *Statistical Learning with Sparsity*, 2015, eq. (11.10);
Wainwright, *High-Dimensional Statistics*, 2019, §7.3.1). -/
def RestrictedEigenvalue (X : Matrix (Fin n) ι ℝ) (S : Finset ι) (κ α : ℝ) : Prop :=
  0 < κ ∧ ∀ Δ ∈ cone S α, κ * ∑ j, Δ j ^ 2 ≤ (1 / n) * ∑ i, (X *ᵥ Δ) i ^ 2

/-- The regularized (Lagrangian) Lasso objective `(1/(2n)) ‖y - X θ‖₂² + lam ‖θ‖₁` (Hastie,
Tibshirani and Wainwright, *Statistical Learning with Sparsity*, 2015, eq. (11.3)). -/
noncomputable def lassoObjective (X : Matrix (Fin n) ι ℝ) (y : Fin n → ℝ) (lam : ℝ)
    (θ : ι → ℝ) : ℝ :=
  (1 / (2 * n)) * ∑ i, (y i - (X *ᵥ θ) i) ^ 2 + lam * ∑ j, |θ j|

omit [DecidableEq ι] in
/-- Expansion of the residual sum of squares at `θ* + Δ` when `y = X θ* + w`. -/
private lemma rss_expand (X : Matrix (Fin n) ι ℝ) (θs Δ : ι → ℝ) (w : Fin n → ℝ) :
    ∑ i, ((X *ᵥ θs + w) i - (X *ᵥ (θs + Δ)) i) ^ 2 =
      ∑ i, w i ^ 2 - 2 * ∑ j, (Xᵀ *ᵥ w) j * Δ j + ∑ i, (X *ᵥ Δ) i ^ 2 := by
  have hcross : ∑ i, w i * (X *ᵥ Δ) i = ∑ j, (Xᵀ *ᵥ w) j * Δ j := by
    have := dotProduct_mulVec w X Δ
    simpa [dotProduct, mulVec_transpose] using this
  have hpt : ∀ i, ((X *ᵥ θs + w) i - (X *ᵥ (θs + Δ)) i) ^ 2 =
      w i ^ 2 - 2 * (w i * (X *ᵥ Δ) i) + (X *ᵥ Δ) i ^ 2 := by
    intro i
    simp only [Pi.add_apply, mulVec_add]
    ring
  simp_rw [hpt, sum_add_distrib, sum_sub_distrib, ← mul_sum, hcross]

omit [Fintype ι] [DecidableEq ι] in
/-- Cauchy–Schwarz on a support set: `‖Δ_S‖₁ ≤ √|S| ‖Δ‖₂` (the step `‖ν_S‖₁ ≤ √k ‖ν‖₂` in the
proof of Theorem 11.1 of Hastie, Tibshirani and Wainwright, *Statistical Learning with Sparsity*,
2015). -/
lemma sum_abs_le_sqrt_card_mul [Fintype ι] (S : Finset ι) (Δ : ι → ℝ) :
    ∑ j ∈ S, |Δ j| ≤ Real.sqrt S.card * Real.sqrt (∑ j, Δ j ^ 2) := by
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  apply Real.le_sqrt_of_sq_le
  have h := sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun j => |Δ j|)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one, sq_abs] at h
  calc (∑ j ∈ S, |Δ j|) ^ 2 ≤ S.card * ∑ j ∈ S, Δ j ^ 2 := h
    _ ≤ S.card * ∑ j, Δ j ^ 2 :=
      mul_le_mul_of_nonneg_left (sum_le_univ_sum_of_nonneg fun j => sq_nonneg _)
        (Nat.cast_nonneg _)

omit [DecidableEq ι] in
/-- Splitting the `ℓ₁` norm along `S` and its complement. -/
private lemma sum_abs_split [DecidableEq ι] (S : Finset ι) (f : ι → ℝ) :
    ∑ j, |f j| = ∑ j ∈ S, |f j| + ∑ j ∈ Sᶜ, |f j| :=
  (sum_add_sum_compl S _).symm

/-- The `ℓ₁` decomposability step: if `θ*` vanishes off `S`, then
`‖θ*‖₁ - ‖θ* + Δ‖₁ ≤ ‖Δ_S‖₁ - ‖Δ_{Sᶜ}‖₁`. -/
private lemma l1_decomp (S : Finset ι) (θs Δ : ι → ℝ) (hsupp : ∀ j ∉ S, θs j = 0) :
    ∑ j, |θs j| - ∑ j, |θs j + Δ j| ≤ ∑ j ∈ S, |Δ j| - ∑ j ∈ Sᶜ, |Δ j| := by
  rw [sum_abs_split S θs, sum_abs_split S (fun j => θs j + Δ j)]
  have h0 : ∑ j ∈ Sᶜ, |θs j| = 0 :=
    sum_eq_zero fun j hj => by simp [hsupp j (mem_compl.mp hj)]
  have h1 : ∑ j ∈ Sᶜ, |θs j + Δ j| = ∑ j ∈ Sᶜ, |Δ j| :=
    sum_congr rfl fun j hj => by simp [hsupp j (mem_compl.mp hj)]
  have h2 : ∑ j ∈ S, |θs j| ≤ ∑ j ∈ S, |θs j + Δ j| + ∑ j ∈ S, |Δ j| := by
    rw [← sum_add_distrib]
    refine sum_le_sum fun j _ => ?_
    calc |θs j| = |(θs j + Δ j) + (-Δ j)| := by ring_nf
      _ ≤ |θs j + Δ j| + |-Δ j| := abs_add_le _ _
      _ = |θs j + Δ j| + |Δ j| := by rw [abs_neg]
  rw [h0, h1]
  linarith

omit [DecidableEq ι] in
/-- The noise term: `|⟨Xᵀ w / n, Δ⟩| ≤ ν ‖Δ‖₁` when `|(Xᵀ w) j| / n ≤ ν` for all `j`. -/
private lemma noise_le (X : Matrix (Fin n) ι ℝ) (w : Fin n → ℝ) (Δ : ι → ℝ) {ν : ℝ}
    (hν : ∀ j, |(Xᵀ *ᵥ w) j| / n ≤ ν) :
    (1 / n) * ∑ j, (Xᵀ *ᵥ w) j * Δ j ≤ ν * ∑ j, |Δ j| := by
  rw [mul_sum, mul_sum]
  refine sum_le_sum fun j _ => ?_
  calc 1 / (n : ℝ) * ((Xᵀ *ᵥ w) j * Δ j) ≤ |1 / (n : ℝ) * ((Xᵀ *ᵥ w) j * Δ j)| := le_abs_self _
    _ = |(Xᵀ *ᵥ w) j| / n * |Δ j| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / n)]; ring
    _ ≤ ν * |Δ j| := by gcongr; exact hν j

/-- **Basic inequality for the Lagrangian Lasso** (Hastie, Tibshirani and Wainwright,
*Statistical Learning with Sparsity*, 2015, Lemma 11.1 and the first inequality of (11.23)).
Let `y = X θ* + w` with `θ*` vanishing off `S`, let `lam > 0` with `|(Xᵀ w) j| / n ≤ lam / 2`
for every `j` (that is, `lam ≥ 2 ‖Xᵀ w / n‖_∞`), and let `θ̂` have Lasso objective at most that
of `θ*`. Then the error `Δ = θ̂ - θ*` lies in the cone `C(S; 3)`, and
`(1/n) ‖X Δ‖₂² ≤ 3 lam ‖Δ_S‖₁`. -/
theorem lasso_basic_inequality (X : Matrix (Fin n) ι ℝ) (S : Finset ι) (θs θhat : ι → ℝ)
    (w : Fin n → ℝ) {lam : ℝ} (hlam : 0 < lam) (hsupp : ∀ j ∉ S, θs j = 0)
    (hnoise : ∀ j, |(Xᵀ *ᵥ w) j| / n ≤ lam / 2)
    (hopt : lassoObjective X (X *ᵥ θs + w) lam θhat ≤ lassoObjective X (X *ᵥ θs + w) lam θs) :
    θhat - θs ∈ cone S 3 ∧
      (1 / n) * ∑ i, (X *ᵥ (θhat - θs)) i ^ 2 ≤ 3 * lam * ∑ j ∈ S, |(θhat - θs) j| := by
  set Δ := θhat - θs with hΔ
  have hθhat : θhat = θs + Δ := by rw [hΔ]; abel
  unfold lassoObjective at hopt
  rw [hθhat, rss_expand] at hopt
  have hself : ∀ i, ((X *ᵥ θs + w) i - (X *ᵥ θs) i) ^ 2 = w i ^ 2 := by
    intro i; simp
  simp_rw [hself] at hopt
  have hdec := l1_decomp S θs Δ hsupp
  have hnz := noise_le X w Δ hnoise
  rw [sum_abs_split S Δ] at hnz
  set A := ∑ j ∈ S, |Δ j|
  set B := ∑ j ∈ Sᶜ, |Δ j|
  set Q := ∑ i, (X *ᵥ Δ) i ^ 2
  set G := ∑ j, (Xᵀ *ᵥ w) j * Δ j
  have hQ : 0 ≤ Q := sum_nonneg fun i _ => sq_nonneg _
  have hθl1 : ∑ j, |(θs + Δ) j| = ∑ j, |θs j + Δ j| := rfl
  rw [hθl1] at hopt
  -- `Q / (2n) ≤ G / n + lam (‖θ*‖₁ - ‖θ̂‖₁)`.
  have key : (1 / n) * Q ≤ 2 * ((1 / n) * G) + 2 * lam * (A - B) := by
    have hn : (1 / (2 * (n : ℝ))) = (1 / 2) * (1 / n) := by
      rw [one_div_mul_one_div]
    rw [hn] at hopt
    nlinarith [hdec, hlam]
  have hQn : 0 ≤ (1 / (n : ℝ)) * Q := mul_nonneg (by positivity) hQ
  refine ⟨?_, ?_⟩
  · change B ≤ 3 * A
    nlinarith
  · -- `(1/n) Q ≤ lam (3A - B) ≤ 3 lam A`.
    have hB : 0 ≤ B := sum_nonneg fun _ _ => abs_nonneg _
    nlinarith

/-- **ℓ₂-error bound for the Lagrangian Lasso** (Hastie, Tibshirani and Wainwright, *Statistical
Learning with Sparsity*, 2015, Theorem 11.1(b); Wainwright, *High-Dimensional Statistics*, 2019,
§7.3.2; after Bickel, Ritov and Tsybakov, Ann. Statist. 37 (2009)). Let `y = X θ* + w`
with `θ*` vanishing off a set `S` of `s` coordinates, suppose `X` satisfies the restricted
eigenvalue condition with constant `κ` over `C(S; 3)`, and let `lam > 0` with
`lam ≥ 2 ‖Xᵀ w / n‖_∞`. Then every minimiser `θ̂` of the Lagrangian Lasso objective satisfies
`‖θ̂ - θ*‖₂ ≤ (3 / κ) √s lam`. -/
theorem lasso_l2_error_le (X : Matrix (Fin n) ι ℝ) (S : Finset ι) (θs θhat : ι → ℝ)
    (w : Fin n → ℝ) {lam κ : ℝ} (hlam : 0 < lam) (hsupp : ∀ j ∉ S, θs j = 0)
    (hRE : RestrictedEigenvalue X S κ 3)
    (hnoise : ∀ j, |(Xᵀ *ᵥ w) j| / n ≤ lam / 2)
    (hmin : ∀ θ, lassoObjective X (X *ᵥ θs + w) lam θhat ≤ lassoObjective X (X *ᵥ θs + w) lam θ) :
    Real.sqrt (∑ j, (θhat j - θs j) ^ 2) ≤ 3 / κ * Real.sqrt S.card * lam := by
  obtain ⟨hcone, hpred⟩ := lasso_basic_inequality X S θs θhat w hlam hsupp hnoise (hmin θs)
  obtain ⟨hκ, hre⟩ := hRE
  set Δ := θhat - θs
  set r := Real.sqrt (∑ j, Δ j ^ 2) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = ∑ j, Δ j ^ 2 := Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)
  have hCS := sum_abs_le_sqrt_card_mul S Δ
  rw [← hr] at hCS
  -- `κ r² ≤ (1/n) ‖XΔ‖² ≤ 3 lam ‖Δ_S‖₁ ≤ 3 lam √s r`.
  have h1 : κ * r ^ 2 ≤ 3 * lam * (Real.sqrt S.card * r) := by
    rw [hrsq]
    calc κ * ∑ j, Δ j ^ 2 ≤ _ := hre Δ hcone
      _ ≤ _ := hpred
      _ ≤ _ := by gcongr
  change r ≤ _
  rcases hr0.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hκ]
    nlinarith

/-- **ℓ₂-error bound for the constrained Lasso** (Hastie, Tibshirani and Wainwright,
*Statistical Learning with Sparsity*, 2015, Theorem 11.1(a); Wainwright, *High-Dimensional
Statistics*, 2019, §7.3.2). Let `y = X θ* + w` with `θ*` vanishing off a set `S` of `s`
coordinates, suppose `X` satisfies the restricted eigenvalue condition with constant `κ` over
`C(S; 1)` (implied by the condition over `C(S; 3)` assumed in the first source), and
let `ν` bound `‖Xᵀ w / n‖_∞`. Then every minimiser `θ̂` of `(1/(2n)) ‖y - X θ‖₂²` over the
`ℓ₁` ball `‖θ‖₁ ≤ R` with radius `R = ‖θ*‖₁` satisfies `‖θ̂ - θ*‖₂ ≤ (4 / κ) √s ν`. -/
theorem constrainedLasso_l2_error_le (X : Matrix (Fin n) ι ℝ) (S : Finset ι) (θs θhat : ι → ℝ)
    (w : Fin n → ℝ) {κ ν : ℝ} (hsupp : ∀ j ∉ S, θs j = 0)
    (hRE : RestrictedEigenvalue X S κ 1)
    (hnoise : ∀ j, |(Xᵀ *ᵥ w) j| / n ≤ ν)
    (hfeas : ∑ j, |θhat j| ≤ ∑ j, |θs j|)
    (hmin : ∀ θ, ∑ j, |θ j| ≤ ∑ j, |θs j| →
      (1 / (2 * n)) * ∑ i, ((X *ᵥ θs + w) i - (X *ᵥ θhat) i) ^ 2 ≤
        (1 / (2 * n)) * ∑ i, ((X *ᵥ θs + w) i - (X *ᵥ θ) i) ^ 2) :
    Real.sqrt (∑ j, (θhat j - θs j) ^ 2) ≤ 4 / κ * Real.sqrt S.card * ν := by
  obtain ⟨hκ, hre⟩ := hRE
  set Δ := θhat - θs with hΔ
  have hθhat : θhat = θs + Δ := by rw [hΔ]; abel
  have hopt := hmin θs le_rfl
  rw [hθhat, rss_expand] at hopt
  have hself : ∀ i, ((X *ᵥ θs + w) i - (X *ᵥ θs) i) ^ 2 = w i ^ 2 := by
    intro i; simp
  simp_rw [hself] at hopt
  have hdec := l1_decomp S θs Δ hsupp
  have hnz := noise_le X w Δ hnoise
  rw [sum_abs_split S Δ] at hnz
  rw [hθhat] at hfeas
  have hfeas' : ∑ j, |θs j + Δ j| ≤ ∑ j, |θs j| := hfeas
  set A := ∑ j ∈ S, |Δ j|
  set B := ∑ j ∈ Sᶜ, |Δ j|
  set Q := ∑ i, (X *ᵥ Δ) i ^ 2
  set G := ∑ j, (Xᵀ *ᵥ w) j * Δ j
  have hQ : 0 ≤ Q := sum_nonneg fun i _ => sq_nonneg _
  have hQn : 0 ≤ (1 / (n : ℝ)) * Q := mul_nonneg (by positivity) hQ
  have hBA : B ≤ A := by linarith
  have hcone : Δ ∈ cone S 1 := by
    change B ≤ 1 * A
    linarith
  -- Basic inequality: `(1/n) Q ≤ 2 (1/n) G`.
  have key : (1 / n) * Q ≤ 2 * ((1 / n) * G) := by
    have hn : (1 / (2 * (n : ℝ))) = (1 / 2) * (1 / n) := by
      rw [one_div_mul_one_div]
    rw [hn] at hopt
    nlinarith
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨j0⟩⟩
  · have hS : S = ∅ := Finset.eq_empty_of_isEmpty S
    simp [hS]
  have hν0 : 0 ≤ ν := le_trans (by positivity) (hnoise j0)
  set r := Real.sqrt (∑ j, Δ j ^ 2) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = ∑ j, Δ j ^ 2 := Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)
  have hCS := sum_abs_le_sqrt_card_mul S Δ
  rw [← hr] at hCS
  -- `κ r² ≤ (1/n) Q ≤ 2 ν (A + B) ≤ 4 ν A ≤ 4 ν √s r`.
  have h1 : κ * r ^ 2 ≤ 4 * ν * (Real.sqrt S.card * r) := by
    rw [hrsq]
    have hA : 0 ≤ A := sum_nonneg fun _ _ => abs_nonneg _
    calc κ * ∑ j, Δ j ^ 2 ≤ (1 / n) * Q := hre Δ hcone
      _ ≤ 2 * (ν * (A + B)) := by linarith
      _ ≤ 4 * ν * A := by nlinarith
      _ ≤ _ := by gcongr
  change r ≤ _
  rcases hr0.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hκ]
    nlinarith

omit [DecidableEq ι] in
/-- **Slow rate for the Lasso prediction error, constant 3** (a sharpening proved here of
Hastie, Tibshirani and Wainwright, *Statistical Learning with Sparsity*, 2015, Theorem 11.2(a)):
let `y = X θ* + w`, let `lam ≥ 2 ‖Xᵀ w / n‖_∞` and let `θ̂` have Lagrangian Lasso objective at
most that of `θ*`. Then `(1/n) ‖X (θ̂ - θ*)‖₂² ≤ 3 lam ‖θ*‖₁`. No sparsity or restricted
eigenvalue condition is needed. The proof uses the modified basic inequality (11.21) of the
source, Hölder's inequality and the triangle inequality `‖Δ‖₁ ≤ ‖θ̂‖₁ + ‖θ*‖₁`. The source's
proof first bounds `‖Δ‖₁ ≤ 4 ‖θ*‖₁` and obtains its stated constant `12`
(`lasso_prediction_error_le_slow`). -/
theorem lasso_prediction_error_le_three (X : Matrix (Fin n) ι ℝ) (θs θhat : ι → ℝ)
    (w : Fin n → ℝ) {lam : ℝ} (hnoise : ∀ j, |(Xᵀ *ᵥ w) j| / n ≤ lam / 2)
    (hopt : lassoObjective X (X *ᵥ θs + w) lam θhat ≤ lassoObjective X (X *ᵥ θs + w) lam θs) :
    (1 / n) * ∑ i, (X *ᵥ (θhat - θs)) i ^ 2 ≤ 3 * lam * ∑ j, |θs j| := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨j0⟩⟩
  · simp [mulVec, dotProduct]
  have hlam : 0 ≤ lam := by
    have h1 := hnoise j0
    have h2 : 0 ≤ |(Xᵀ *ᵥ w) j0| / n := by positivity
    linarith
  set Δ := θhat - θs with hΔ
  have hθhat : θhat = θs + Δ := by rw [hΔ]; abel
  unfold lassoObjective at hopt
  rw [hθhat, rss_expand] at hopt
  have hself : ∀ i, ((X *ᵥ θs + w) i - (X *ᵥ θs) i) ^ 2 = w i ^ 2 := by
    intro i; simp
  simp_rw [hself] at hopt
  have hnz := noise_le X w Δ hnoise
  have htri : ∑ j, |Δ j| ≤ ∑ j, |θs j + Δ j| + ∑ j, |θs j| := by
    rw [← sum_add_distrib]
    refine sum_le_sum fun j _ => ?_
    calc |Δ j| = |(θs j + Δ j) + (-θs j)| := by ring_nf
      _ ≤ |θs j + Δ j| + |-θs j| := abs_add_le _ _
      _ = |θs j + Δ j| + |θs j| := by rw [abs_neg]
  have hθl1 : ∑ j, |(θs + Δ) j| = ∑ j, |θs j + Δ j| := rfl
  rw [hθl1] at hopt
  have hn : (1 / (2 * (n : ℝ))) = (1 / 2) * (1 / n) := by
    rw [one_div_mul_one_div]
  rw [hn] at hopt
  have hθh : 0 ≤ ∑ j, |θs j + Δ j| := sum_nonneg fun _ _ => abs_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left htri hlam, mul_nonneg hlam hθh]

omit [DecidableEq ι] in
/-- **Slow rate for the Lasso prediction error** (Hastie, Tibshirani and Wainwright,
*Statistical Learning with Sparsity*, 2015, Theorem 11.2(a)): for the Lagrangian Lasso with
`lam ≥ 2 ‖Xᵀ w / n‖_∞` (so `lam ≥ 0`, assumed explicitly to cover an empty index type) and
`‖θ*‖₁ ≤ R₁`, every minimiser `θ̂` satisfies `(1/n) ‖X (θ̂ - θ*)‖₂² ≤ 12 R₁ lam`. -/
theorem lasso_prediction_error_le_slow (X : Matrix (Fin n) ι ℝ) (θs θhat : ι → ℝ)
    (w : Fin n → ℝ) {lam R₁ : ℝ} (hlam : 0 ≤ lam) (hnoise : ∀ j, |(Xᵀ *ᵥ w) j| / n ≤ lam / 2)
    (hR : ∑ j, |θs j| ≤ R₁)
    (hmin : ∀ θ, lassoObjective X (X *ᵥ θs + w) lam θhat ≤ lassoObjective X (X *ᵥ θs + w) lam θ) :
    (1 / n) * ∑ i, (X *ᵥ (θhat - θs)) i ^ 2 ≤ 12 * R₁ * lam := by
  have h3 := lasso_prediction_error_le_three X θs θhat w hnoise (hmin θs)
  have hθs : 0 ≤ ∑ j, |θs j| := sum_nonneg fun _ _ => abs_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hR hlam, mul_nonneg hlam hθs]

/-- **Fast rate for the Lasso prediction error** (Hastie, Tibshirani and Wainwright,
*Statistical Learning with Sparsity*, 2015, Theorem 11.2(b)): if `θ*` vanishes off `S`, `X`
satisfies the restricted eigenvalue condition with constant `κ` over `C(S; 3)`, `lam > 0` and
`lam ≥ 2 ‖Xᵀ w / n‖_∞`, then every minimiser `θ̂` of the Lagrangian Lasso satisfies
`(1/n) ‖X (θ̂ - θ*)‖₂² ≤ (9 / κ) |S| lam²`. -/
theorem lasso_prediction_error_le_fast (X : Matrix (Fin n) ι ℝ) (S : Finset ι)
    (θs θhat : ι → ℝ) (w : Fin n → ℝ) {lam κ : ℝ} (hlam : 0 < lam)
    (hsupp : ∀ j ∉ S, θs j = 0) (hRE : RestrictedEigenvalue X S κ 3)
    (hnoise : ∀ j, |(Xᵀ *ᵥ w) j| / n ≤ lam / 2)
    (hmin : ∀ θ, lassoObjective X (X *ᵥ θs + w) lam θhat ≤ lassoObjective X (X *ᵥ θs + w) lam θ) :
    (1 / n) * ∑ i, (X *ᵥ (θhat - θs)) i ^ 2 ≤ 9 / κ * S.card * lam ^ 2 := by
  obtain ⟨hcone, hpred⟩ := lasso_basic_inequality X S θs θhat w hlam hsupp hnoise (hmin θs)
  obtain ⟨hκ, hre⟩ := hRE
  set Δ := θhat - θs
  set P := (1 / (n : ℝ)) * ∑ i, (X *ᵥ Δ) i ^ 2 with hP
  have hP0 : 0 ≤ P := mul_nonneg (by positivity) (sum_nonneg fun _ _ => sq_nonneg _)
  set r := Real.sqrt (∑ j, Δ j ^ 2) with hr
  have hrsq : r ^ 2 = ∑ j, Δ j ^ 2 := Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)
  have hCS := sum_abs_le_sqrt_card_mul S Δ
  rw [← hr] at hCS
  have hsq : Real.sqrt S.card ^ 2 = S.card := Real.sq_sqrt (Nat.cast_nonneg _)
  -- `P ≤ 3 lam √s r` and `κ r² ≤ P`, hence `P² ≤ 9 lam² s r² ≤ 9 lam² s P / κ`.
  have h1 : P ≤ 3 * lam * (Real.sqrt S.card * r) :=
    hpred.trans (by gcongr)
  have h2 : κ * r ^ 2 ≤ P := by rw [hrsq]; exact hre Δ hcone
  have h3 : P ^ 2 ≤ 9 * lam ^ 2 * S.card * r ^ 2 := by
    calc P ^ 2 ≤ (3 * lam * (Real.sqrt S.card * r)) ^ 2 := pow_le_pow_left₀ hP0 h1 2
      _ = 9 * lam ^ 2 * Real.sqrt S.card ^ 2 * r ^ 2 := by ring
      _ = 9 * lam ^ 2 * S.card * r ^ 2 := by rw [hsq]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hκ]
  rcases hP0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]; positivity
  · have h4 : P ^ 2 * κ ≤ 9 * lam ^ 2 * S.card * P := by
      have hs : (0 : ℝ) ≤ 9 * lam ^ 2 * S.card := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h2 hs]
    nlinarith

end

end MathlibExt.Probability.Statistics.LassoRestrictedEigenvalue
