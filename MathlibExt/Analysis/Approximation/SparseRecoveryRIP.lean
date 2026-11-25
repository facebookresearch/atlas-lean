/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Approximation.SparseRestrictedIsometry

/-!
# Noiseless sparse recovery in ℓ₁

Under the restricted isometry property, `sum_abs_sub_le_of_hasRIP` bounds the ℓ₁ error of
basis pursuit by the ℓ₁ mass outside any set of at most `s` coordinates.
-/

@[expose] public section

open Finset Matrix MathlibExt.Analysis.Approximation.SparseRestrictedIsometry

namespace MathlibExt.Analysis.Approximation.SparseRecoveryRIPWanted

/-- The cone constraint obtained by comparing the ℓ₁ norms on `S` and its complement. -/
private lemma sum_abs_sub_compl_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {x xhat : ι → ℝ} (hle : ∑ j, |xhat j| ≤ ∑ j, |x j|) (S : Finset ι) :
    ∑ j ∈ Sᶜ, |xhat j - x j| ≤ ∑ j ∈ S, |xhat j - x j| + 2 * ∑ j ∈ Sᶜ, |x j| := by
  have hhead := sum_le_sum (s := S) fun j _ =>
    (abs_sub_abs_le_abs_sub (x j) (xhat j)).trans_eq (abs_sub_comm _ _)
  have htail := sum_le_sum (s := Sᶜ) fun j _ => abs_sub (xhat j) (x j)
  rw [sum_sub_distrib] at hhead
  rw [sum_add_distrib] at htail
  rw [← sum_add_sum_compl S (fun j => |xhat j|), ← sum_add_sum_compl S (fun j => |x j|)] at hle
  linarith

/-- **Noiseless recovery, `ℓ₁` error** (E. J. Candès, *The restricted isometry property and its
implications for compressed sensing*, C. R. Acad. Sci. Paris, Ser. I 346 (2008) 589–592,
Theorem 1.2, eq. (4)): let `s ≥ 1` and let `Φ` have the restricted isometry property of order
`2 s` with a constant `δ < √2 - 1`. Let `xhat` be a solution of `min ‖x̃‖₁` subject to
`Φ x̃ = Φ x`. Then `‖xhat - x‖₁ ≤ C₀ ‖x - x_s‖₁` with `C₀ = 2 (1 + ρ) / (1 - ρ)` and
`ρ = √2 δ / (1 - δ)`; here `‖x - x_s‖₁` is replaced by `∑_{j ∉ S} |x j|` for an arbitrary set
`S` of at most `s` indices, an equivalent formulation since `x_s` is the best `s`-term
approximation of `x`. -/
theorem sum_abs_sub_le_of_hasRIP {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    {Φ : Matrix (Fin m) ι ℝ} {s : ℕ} (hs : 1 ≤ s) {δ : ℝ} (hΦ : HasRIP Φ (2 * s) δ)
    (hδ : δ < √2 - 1) {x xhat : ι → ℝ} (hfeas : Φ *ᵥ xhat = Φ *ᵥ x)
    (hmin : ∀ w : ι → ℝ, Φ *ᵥ w = Φ *ᵥ x → ∑ j, |xhat j| ≤ ∑ j, |w j|)
    {S : Finset ι} (hS : #S ≤ s) :
    ∑ j, |xhat j - x j| ≤
      2 * (1 + √2 * δ / (1 - δ)) / (1 - √2 * δ / (1 - δ)) * ∑ j ∈ Sᶜ, |x j| := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Finset.univ_eq_empty, Finset.eq_empty_of_isEmpty Sᶜ]
  have hδ1 : δ < 1 := by
    have : √(2 : ℝ) < 2 := by norm_num [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
    linarith
  set ρ := √2 * δ / (1 - δ)
  have hρ0 : 0 ≤ ρ :=
    div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hΦ.nonneg (by omega))) (sub_nonneg.mpr hδ1.le)
  have hρ : ρ < 1 := by
    rw [div_lt_one (sub_pos.mpr hδ1)]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      mul_pos (sub_pos.mpr hδ) (show 0 < √(2 : ℝ) + 1 by positivity)]
  have hker : Φ *ᵥ (xhat - x) = 0 := by rw [mulVec_sub, hfeas, sub_self]
  have hnull := sum_abs_le_of_mulVec_eq_zero hs hΦ hδ1 hker hS
  change ∑ j ∈ S, |xhat j - x j| ≤ ρ * ∑ j ∈ Sᶜ, |xhat j - x j| at hnull
  have hcone := sum_abs_sub_compl_le (hmin x rfl) S
  have htail : ∑ j ∈ Sᶜ, |xhat j - x j| ≤ (2 * ∑ j ∈ Sᶜ, |x j|) / (1 - ρ) := by
    apply (le_div_iff₀ (sub_pos.mpr hρ)).2
    linarith only [hcone, hnull]
  calc
    ∑ j, |xhat j - x j| = ∑ j ∈ S, |xhat j - x j| + ∑ j ∈ Sᶜ, |xhat j - x j| :=
      (sum_add_sum_compl S _).symm
    _ ≤ (1 + ρ) * ∑ j ∈ Sᶜ, |xhat j - x j| := by linarith only [hnull]
    _ ≤ (1 + ρ) * ((2 * ∑ j ∈ Sᶜ, |x j|) / (1 - ρ)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = _ := by ring

end MathlibExt.Analysis.Approximation.SparseRecoveryRIPWanted
