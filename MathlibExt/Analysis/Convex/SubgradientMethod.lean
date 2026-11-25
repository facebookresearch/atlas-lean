/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The subgradient method

For nonsmooth convex objectives, gradient steps with decreasing step sizes `γₖ ∝ 1 / √k` reach an
objective gap of order `log t / √t` after `t` steps, the rate of the subgradient method and, in
expectation, of stochastic gradient descent (F. Bach, *Learning Theory from First Principles*,
MIT Press (2024), Sections 5.3 and 5.4).
-/

@[expose] public section

open Real
open scoped RealInnerProductSpace

namespace MetaMathlibExt

/-- **Convergence of the subgradient method.** Let `f : E → ℝ` on a real inner product space,
and let `X k` be iterates of the subgradient method with the step `γₖ = D / (B √(k + 1))`:
`X (k + 1) = X k - γₖ gₖ`, where each `gₖ` is a subgradient of `f` at `X k`
(`f y ≥ f (X k) + ⟪gₖ, y - X k⟫` for all `y`) with `‖gₖ‖ ≤ B`. If `‖X 0 - x⋆‖ ≤ D`, then for every
`t ≥ 1` some iterate among the first `t` satisfies
`f (X k) - f x⋆ ≤ D B (2 + log t) / (2 √t)`.

For a convex `B`-Lipschitz function with a minimizer `x⋆` every subgradient has norm at most `B`,
which is the source's setting.
Source: F. Bach, *Learning Theory from First Principles*, MIT Press (2024), Section 5.3,
Proposition 5.6 (stated for convex `B`-Lipschitz functions on `ℝ^d` with a minimizer at distance
at most `D` from the initial point; only the subgradient inequality at the iterates, the bound on
the subgradients and the distance bound are used).
Proof: as in the source, `‖X (k+1) - x⋆‖² ≤ ‖X k - x⋆‖² - 2 γₖ (f (X k) - f x⋆) + γₖ² B²`;
summing, `∑ γₖ (f (X k) - f x⋆) ≤ D² / 2 + B² ∑ γₖ² / 2` with `∑ₖ<t γₖ² ≤ (D / B)² (1 + log t)`
(harmonic numbers) and `∑ₖ<t γₖ ≥ D √t / B`, so the smallest gap is at most the weighted average. -/
theorem subgradient_method_rate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → ℝ} {B D : ℝ} (hB : 0 < B) (hD : 0 < D)
    {X g : ℕ → E} (hsub : ∀ k y, f (X k) + ⟪g k, y - X k⟫ ≤ f y) (hg : ∀ k, ‖g k‖ ≤ B)
    {xstar : E} (hdist : ‖X 0 - xstar‖ ≤ D)
    (hX : ∀ k, X (k + 1) = X k - (D / (B * √((k : ℝ) + 1))) • g k) {t : ℕ} (ht : 0 < t) :
    ∃ k < t, f (X k) - f xstar ≤ D * B * (2 + log t) / (2 * √t) := by
  set γ : ℕ → ℝ := fun k => D / (B * √((k : ℝ) + 1)) with hγ
  have hγpos : ∀ k, 0 < γ k := fun k => by positivity
  -- One step of the distance recursion.
  have hstep : ∀ k, 2 * γ k * (f (X k) - f xstar) ≤
      ‖X k - xstar‖ ^ 2 - ‖X (k + 1) - xstar‖ ^ 2 + γ k ^ 2 * B ^ 2 := by
    intro k
    have hlin : f (X k) - f xstar ≤ ⟪g k, X k - xstar⟫ := by
      have := hsub k xstar
      have h2 : ⟪g k, xstar - X k⟫ = -⟪g k, X k - xstar⟫ := by
        rw [← inner_neg_right, neg_sub]
      linarith
    have hnorm : ‖X (k + 1) - xstar‖ ^ 2 =
        ‖X k - xstar‖ ^ 2 - 2 * γ k * ⟪g k, X k - xstar⟫ + γ k ^ 2 * ‖g k‖ ^ 2 := by
      rw [hX k, show X k - γ k • g k - xstar = (X k - xstar) - γ k • g k by abel,
        norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (hγpos k), real_inner_comm]
      ring
    have hg2 : ‖g k‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hg k) 2
    have := hγpos k
    nlinarith [mul_le_mul_of_nonneg_left hg2 (sq_nonneg (γ k))]
  -- Summing the recursion.
  have hsum : 2 * ∑ k ∈ Finset.range t, γ k * (f (X k) - f xstar) ≤
      D ^ 2 + B ^ 2 * ∑ k ∈ Finset.range t, γ k ^ 2 := by
    have htel : ∀ n, 2 * ∑ k ∈ Finset.range n, γ k * (f (X k) - f xstar) ≤
        ‖X 0 - xstar‖ ^ 2 - ‖X n - xstar‖ ^ 2 + B ^ 2 * ∑ k ∈ Finset.range n, γ k ^ 2 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        nlinarith [hstep n]
    have hD2 : ‖X 0 - xstar‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdist 2
    nlinarith [htel t, sq_nonneg ‖X t - xstar‖]
  -- `∑ γ_k² ≤ (D / B)² (1 + log t)`.
  have hsq : ∑ k ∈ Finset.range t, γ k ^ 2 ≤ D ^ 2 / B ^ 2 * (1 + log t) := by
    have hh : ∑ k ∈ Finset.range t, γ k ^ 2 = D ^ 2 / B ^ 2 * (harmonic t : ℝ) := by
      rw [harmonic, Rat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hγ]
      simp only
      rw [div_pow, mul_pow, sq_sqrt (by positivity)]
      push_cast
      field_simp
    rw [hh]
    gcongr
    exact harmonic_le_one_add_log t
  -- `∑ γ_k ≥ D √t / B`.
  have htpos : (0 : ℝ) < t := Nat.cast_pos.mpr ht
  have hlin : D * √t / B ≤ ∑ k ∈ Finset.range t, γ k := by
    have hle : ∀ k ∈ Finset.range t, D / (B * √t) ≤ γ k := by
      intro k hk
      have hk' : (k : ℝ) + 1 ≤ t := by
        have := Finset.mem_range.mp hk; exact_mod_cast this
      rw [hγ]
      apply div_le_div_of_nonneg_left hD.le (by positivity)
      gcongr
    calc D * √t / B = ∑ _k ∈ Finset.range t, D / (B * √t) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          have hs : 0 < √(t : ℝ) := sqrt_pos.mpr htpos
          field_simp
          rw [sq_sqrt htpos.le]
      _ ≤ _ := Finset.sum_le_sum hle
  -- Conclude by contradiction.
  by_contra hcon
  push Not at hcon
  set m := D * B * (2 + log t) / (2 * √t)
  have hlt : m * ∑ k ∈ Finset.range t, γ k < ∑ k ∈ Finset.range t, γ k * (f (X k) - f xstar) := by
    rw [Finset.mul_sum]
    apply Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr ht.ne')
    intro k hk
    rw [mul_comm]
    exact mul_lt_mul_of_pos_left (hcon k (Finset.mem_range.mp hk)) (hγpos k)
  have hlog : 0 ≤ log t := log_nonneg (by exact_mod_cast ht)
  have hm : 0 ≤ m := by positivity
  have hs : 0 < √(t : ℝ) := sqrt_pos.mpr htpos
  have hmlin : m * (D * √t / B) = D ^ 2 * (2 + log t) / 2 := by
    simp only [m]; field_simp
  have := mul_le_mul_of_nonneg_left hlin hm
  have hB2 : B ^ 2 * (D ^ 2 / B ^ 2 * (1 + log t)) = D ^ 2 * (1 + log t) := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg B)]

end MetaMathlibExt
