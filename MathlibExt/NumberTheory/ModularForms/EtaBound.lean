/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.Modular
public import Mathlib.NumberTheory.ModularForms.Discriminant

/-!
# An explicit upper bound for `‖η(τ)‖ ^ 24 (Im τ) ^ 6`

The function `τ ↦ ‖Δ(τ)‖ (Im τ) ^ 6` on the upper half-plane, where `Δ = η ^ 24` is the modular
discriminant (`ModularForm.discriminant`), is invariant under `SL(2, ℤ)` and bounded. Through the
formula expressing the Faltings height of an elliptic curve over a number field in terms of its
minimal discriminant and the values `‖Δ(τ_σ)‖ (Im τ_σ) ^ 6` at its complex periods
(J. H. Silverman, "Heights and elliptic curves", in G. Cornell and J. H. Silverman (eds.),
*Arithmetic Geometry*, Springer, 1986, Proposition 1.1, p. 254, cited as stated), an explicit upper
bound for this function is the analytic input of explicit lower bounds for the Faltings height of
elliptic curves. The constant `1 / 64` is exactly what the case `g = 1` of Bost's lower bound
`h_F ≥ -(g/2) log (2π²)` needs (É. Gaudron and G. Rémond, Comment. Math. Helv. 89 (2014),
Corollaire 8.4, p. 400, cited as stated); it is not optimal.

## Main results

* `ModularForm.norm_tprod_one_sub_pow_le`: `‖∏' n, (1 - q ^ (n + 1))‖ ≤ exp (‖q‖ / (1 - ‖q‖))`
  for `‖q‖ < 1`.
* `ModularForm.norm_eta_le`: `‖η(τ)‖ ≤ exp (-π Im τ / 12) · exp (r / (1 - r))`, where
  `r = exp (-2π Im τ)`.
* `ModularForm.norm_eta_pow_mul_im_pow_le_of_mem_fd`: `‖η(τ)‖ ^ 24 (Im τ) ^ 6 ≤ 1 / 64` for `τ` in
  the standard fundamental domain `ModularGroup.fd`.
* `ModularForm.norm_eta_pow_mul_im_pow_le`: the same bound for every `τ` in the upper half-plane,
  by `SL(2, ℤ)`-invariance of `‖Δ(τ)‖ (Im τ) ^ 6`.

## Method

The product `∏ (1 - q ^ (n + 1))` is bounded termwise by `‖1 - x‖ ≤ 1 + ‖x‖ ≤ exp ‖x‖` and the
geometric series `∑ r ^ (n + 1) = r / (1 - r)`. On the fundamental domain `Im τ ≥ √3 / 2`, so
`t = 2π Im τ ≥ 5`; then `(Im τ) ^ 6 exp (-t) ≤ 720 / (2π) ^ 6` (from `t ^ 6 / 6! ≤ exp t`) and
`exp (24 r / (1 - r)) ≤ 71 / 59` (from `e ^ 5 ≥ 143`), with the certified bounds `π > 3.14` and
`e > 2.7`. The `SL(2, ℤ)`-invariance uses the weight-12 invariance of `Δ` under the generators
`S` and `T` (`ModularForm.discriminant_S_invariant`, `ModularForm.discriminant_T_invariant`) and
`Im (g • τ) = Im τ / |c τ + d| ^ 2`.
-/

@[expose] public section

open Complex UpperHalfPlane

open scoped Real

namespace ModularForm

/-- For `‖q‖ < 1`, the infinite product `∏' n, (1 - q ^ (n + 1))` has norm at most
`exp (‖q‖ / (1 - ‖q‖))`. -/
theorem norm_tprod_one_sub_pow_le {q : ℂ} (hq : ‖q‖ < 1) :
    ‖∏' n : ℕ, (1 - q ^ (n + 1))‖ ≤ Real.exp (‖q‖ / (1 - ‖q‖)) := by
  have hm := (multipliable_one_sub_pow hq).hasProd.norm
  have hs : HasSum (fun n : ℕ ↦ ‖q‖ ^ (n + 1)) (‖q‖ / (1 - ‖q‖)) := by
    convert (hasSum_geometric_of_lt_one (norm_nonneg q) hq).mul_left ‖q‖ using 1
    · ext n; ring
    · rw [div_eq_mul_inv]
  refine le_of_tendsto' hm fun s ↦ ?_
  rw [norm_prod]
  calc ∏ n ∈ s, ‖1 - q ^ (n + 1)‖ ≤ ∏ n ∈ s, Real.exp (‖q‖ ^ (n + 1)) := by
        refine Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun n _ ↦ ?_
        calc ‖1 - q ^ (n + 1)‖ ≤ ‖(1 : ℂ)‖ + ‖q ^ (n + 1)‖ := norm_sub_le _ _
          _ = ‖q‖ ^ (n + 1) + 1 := by rw [norm_one, norm_pow, add_comm]
          _ ≤ Real.exp (‖q‖ ^ (n + 1)) := Real.add_one_le_exp _
    _ = Real.exp (∑ n ∈ s, ‖q‖ ^ (n + 1)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (‖q‖ / (1 - ‖q‖)) :=
        Real.exp_le_exp.2 (sum_le_hasSum s (fun _ _ ↦ by positivity) hs)

/-- An explicit upper bound for the Dedekind eta function: for every `τ` in the upper half-plane,
with `r = exp (-2π Im τ)` (the absolute value of `q = e ^ (2πiτ)`),
`‖η(τ)‖ ≤ exp (-π Im τ / 12) · exp (r / (1 - r))`. Here `exp (-π Im τ / 12) = ‖q ^ (1 / 24)‖` and
`exp (r / (1 - r))` bounds the norm of the product `∏' n, (1 - q ^ (n + 1))`. -/
theorem norm_eta_le (τ : ℍ) :
    ‖eta τ‖ ≤ Real.exp (-π * τ.im / 12) *
      Real.exp (Real.exp (-2 * π * τ.im) / (1 - Real.exp (-2 * π * τ.im))) := by
  have hq : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ = Real.exp (-2 * π * τ.im) := by
    rw [Function.Periodic.norm_qParam, div_one, coe_im]
  have hlt : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1 := by
    simpa using norm_qParam_lt_one 1 τ
  rw [eta, norm_mul, Function.Periodic.norm_qParam, coe_im]
  have h24 : -2 * π * τ.im / 24 = -π * τ.im / 12 := by ring
  rw [h24]
  gcongr
  rw [← hq]
  exact norm_tprod_one_sub_pow_le hlt

/-- `143 ≤ exp 5`, from `2.7 < e`. -/
private lemma le_exp_five : (143 : ℝ) ≤ Real.exp 5 := by
  have h := Real.exp_one_gt_d9
  have h1 : (2.7 : ℝ) ^ 5 ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) (by linarith) 5
  rw [Real.exp_one_pow] at h1
  norm_num at h1 ⊢
  linarith

/-- An explicit upper bound for `‖η(τ)‖ ^ 24 (Im τ) ^ 6 = ‖Δ(τ)‖ (Im τ) ^ 6` on the standard
fundamental domain: for every `τ ∈ ModularGroup.fd` (so `|Re τ| ≤ 1 / 2` and `|τ| ≥ 1`),
`‖η(τ)‖ ^ 24 (Im τ) ^ 6 ≤ 1 / 64`. The constant `1 / 64` is explicit and not optimal; only the
consequence `Im τ ≥ √3 / 2` of `τ ∈ ModularGroup.fd` is used. -/
theorem norm_eta_pow_mul_im_pow_le_of_mem_fd (τ : ℍ) (hτ : τ ∈ ModularGroup.fd) :
    ‖eta τ‖ ^ 24 * τ.im ^ 6 ≤ 1 / 64 := by
  set y := τ.im with hy_def
  have hy0 : 0 < y := τ.im_pos
  have hy : 3 ≤ 4 * y ^ 2 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hτ
  have hpi := Real.pi_gt_d2
  set t := 2 * π * y with ht_def
  have ht0 : 0 < t := by positivity
  have ht5 : 5 ≤ t := by
    have hsq : 25 < t ^ 2 := by
      have : t ^ 2 = π ^ 2 * (4 * y ^ 2) := by rw [ht_def]; ring
      rw [this]
      nlinarith
    nlinarith
  set E := Real.exp t with hE_def
  have hE0 : 0 < E := Real.exp_pos t
  have hE143 : 143 ≤ E := le_exp_five.trans (Real.exp_le_exp.2 ht5)
  have hpoly : t ^ 6 / 720 ≤ E := by
    have := Real.pow_div_factorial_le_exp t ht0.le 6
    simpa [Nat.factorial] using this
  set r := Real.exp (-2 * π * y) with hr_def
  have hrE : r = E⁻¹ := by
    rw [hr_def, hE_def, ← Real.exp_neg]; congr 1; ring
  have hr0 : 0 < r := Real.exp_pos _
  have hr143 : r ≤ 1 / 143 := by
    rw [hrE, one_div]; exact inv_anti₀ (by norm_num) hE143
  set x := 24 * (r / (1 - r)) with hx_def
  have hx0 : 0 < x := by
    have : 0 < 1 - r := by linarith
    positivity
  have hx : x ≤ 12 / 71 := by
    rw [hx_def, mul_div_assoc', div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hexpx : Real.exp x ≤ 71 / 59 := by
    have h1 := Real.exp_bound_div_one_sub_of_interval' hx0 (by linarith)
    have h2 : 1 / (1 - x) ≤ 71 / 59 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    linarith
  have hη : ‖eta τ‖ ^ 24 ≤ E⁻¹ * Real.exp x := by
    calc ‖eta τ‖ ^ 24
        ≤ (Real.exp (-π * y / 12) * Real.exp (r / (1 - r))) ^ 24 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_eta_le τ) 24
      _ = Real.exp (-2 * π * y) * Real.exp x := by
          rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, hx_def]
          congr 2
          push_cast; ring
      _ = E⁻¹ * Real.exp x := by rw [← hr_def, hrE]
  have hA : y ^ 6 * E⁻¹ ≤ 720 / 6.28 ^ 6 := by
    have h1 : y ^ 6 * E⁻¹ ≤ 720 / (2 * π) ^ 6 := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ hE0 (by positivity)]
      have : t ^ 6 = (2 * π) ^ 6 * y ^ 6 := by rw [ht_def]; ring
      rw [div_le_iff₀ (by norm_num), this] at hpoly
      linarith
    have h2 : (720 : ℝ) / (2 * π) ^ 6 ≤ 720 / 6.28 ^ 6 := by
      gcongr
      linarith
    linarith
  calc ‖eta τ‖ ^ 24 * y ^ 6 ≤ E⁻¹ * Real.exp x * y ^ 6 := by gcongr
    _ = y ^ 6 * E⁻¹ * Real.exp x := by ring
    _ ≤ 720 / 6.28 ^ 6 * (71 / 59) := by
        gcongr
    _ ≤ 1 / 64 := by norm_num

/-- An explicit upper bound for `‖η(τ)‖ ^ 24 (Im τ) ^ 6 = ‖Δ(τ)‖ (Im τ) ^ 6` on the whole upper
half-plane: for every `τ` in the upper half-plane, `‖η(τ)‖ ^ 24 (Im τ) ^ 6 ≤ 1 / 64`. It follows
from the bound on the fundamental domain (`ModularGroup.fd`) and the `SL(2, ℤ)`-invariance of
`‖Δ(τ)‖ (Im τ) ^ 6`. The constant `1 / 64` is explicit and not optimal. -/
theorem norm_eta_pow_mul_im_pow_le (τ : ℍ) :
    ‖eta τ‖ ^ 24 * τ.im ^ 6 ≤ 1 / 64 := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
  have hinv := congr_fun (SlashInvariantForm.slash_action_generators_SL2Z
    discriminant_S_invariant discriminant_T_invariant g) τ
  rw [SL_slash_apply] at hinv
  have him := ModularGroup.im_smul_eq_div_normSq g τ
  have h := norm_eta_pow_mul_im_pow_le_of_mem_fd _ hg
  generalize g • τ = σ at hinv him h
  generalize denom (Matrix.SpecialLinearGroup.toGL
    ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (τ : ℂ) = d at hinv him
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp at him
    linarith [σ.im_pos]
  have hnd : 0 < ‖d‖ := norm_pos_iff.2 hd0
  rw [Complex.normSq_eq_norm_sq] at him
  have hΔ : ‖eta τ‖ ^ 24 = ‖eta σ‖ ^ 24 / ‖d‖ ^ 12 := by
    have := congr_arg norm hinv
    simp only [discriminant, norm_mul, norm_pow, norm_zpow] at this
    rw [← this, zpow_neg, div_eq_mul_inv]
    rfl
  rw [hΔ]
  rw [him] at h
  calc ‖eta σ‖ ^ 24 / ‖d‖ ^ 12 * τ.im ^ 6
      = ‖eta σ‖ ^ 24 * (τ.im / ‖d‖ ^ 2) ^ 6 := by field_simp
    _ ≤ 1 / 64 := h

end ModularForm
