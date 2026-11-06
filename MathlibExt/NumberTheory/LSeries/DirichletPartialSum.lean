/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import MathlibExt.NumberTheory.DirichletCharacter.PolyaVinogradov

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Harmonic.Bounds
import MathlibExt.NumberTheory.DirichletCharacter.DivisorSum

/-!
# Dirichlet L-functions from short partial sums

Let `Φ : ZMod q → ℂ` have total sum `0`, so that its L-function `L(s, Φ)` is entire, and suppose
the partial sums `∑_{n ≤ N} Φ n` are bounded by `B`. Abel summation on `Re s > 1` and the
identity theorem give, for `Re s > 0` and `x ≥ 1`,

`|L(s, Φ) - ∑_{n ≤ x} Φ n n^{-s}| ≤ 2 B (|s| / Re s) x^{-Re s}`.

With the Pólya–Vinogradov inequality this approximates `L(s, χ)` for a nontrivial Dirichlet
character `χ` modulo `q` by a sum of length `x` with error `≪ |s| √q log q / (Re s · x^{Re s})`.
Applied to `Φ = ∑_{χ ≠ 1} χ` with `x = q`, it evaluates the average of `L(s, χ)` over the
nontrivial characters modulo `q`.

## Main statements

* `ZMod.LFunction_sum`: `L(s, Φ)` is linear in `Φ`.
* `ZMod.norm_LFunction_sub_sum_Icc_le`: the truncation bound for `L(s, Φ)`.
* `DirichletCharacter.norm_LFunction_sub_sum_Icc_le`:
  `|L(s, χ) - ∑_{n ≤ x} χ n n^{-s}| ≤ 4 |s| √q (1 + log q) / (Re s · x^{Re s})` for `χ ≠ 1`.
* `DirichletCharacter.norm_LFunction_one_sub_sum_Icc_le`:
  `|L(1, χ) - ∑_{n ≤ x} χ n / n| ≤ 4 √q (1 + log q) / x` for `χ ≠ 1`.
* `DirichletCharacter.norm_sum_LFunction_one_sub_totient_le`:
  `|∑_{χ ≠ 1} L(1, χ) - φ(q)| ≤ 5 + log q`.
* `DirichletCharacter.norm_sum_LFunction_sub_totient_le`:
  `|∑_{χ ≠ 1} L(σ, χ) - φ(q)| ≤ 7 q^{3/2 - σ}` for `0 < σ ≤ 3/2`.
-/

@[expose] public section

open Finset Filter

open scoped Topology

namespace Complex

/-- The derivative of `u ↦ u ^ (-w)` on the positive reals, as a complex power. -/
theorem hasDerivAt_ofReal_cpow_neg (w : ℂ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ (-w)) (-w * (u : ℂ) ^ (-w - 1)) u :=
  (hasStrictDerivAt_cpow_const (ofReal_mem_slitPlane.mpr hu)).hasDerivAt.comp_ofReal

private lemma norm_neg_mul_ofReal_cpow (w : ℂ) {u : ℝ} (hu : 0 < u) :
    ‖-w * (u : ℂ) ^ (-w - 1)‖ = ‖w‖ * u ^ (-w.re - 1) := by
  rw [norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hu]
  simp

/-- **Telescoping bound for consecutive complex powers.** For `Re w > 0` and `n ≥ 1`,
`‖n^{-w} - (n + 1)^{-w}‖ ≤ (‖w‖ / Re w) (n^{-Re w} - (n + 1)^{-Re w})`. -/
theorem norm_ofReal_cpow_neg_sub_succ_le {w : ℂ} (hw : 0 < w.re) {n : ℝ} (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-w) - ((n + 1 : ℝ) : ℂ) ^ (-w)‖ ≤
      ‖w‖ / w.re * (n ^ (-w.re) - (n + 1) ^ (-w.re)) := by
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (f := fun y : ℝ ↦ (y : ℂ) ^ (-w) - (n : ℂ) ^ (-w))
    (f' := fun y ↦ -w * (y : ℂ) ^ (-w - 1))
    (B := fun y ↦ ‖w‖ / w.re * (n ^ (-w.re) - y ^ (-w.re)))
    (B' := fun y ↦ ‖w‖ * y ^ (-w.re - 1)) (a := n) (b := n + 1)
    (fun y hy ↦ ((hasDerivAt_ofReal_cpow_neg w (by linarith [hy.1] : 0 < y)).continuousAt.sub
      continuousAt_const).continuousWithinAt)
    (fun y hy ↦
      ((hasDerivAt_ofReal_cpow_neg w (by linarith [hy.1] : 0 < y)).sub_const _).hasDerivWithinAt)
    (by simp)
    (fun y hy ↦ (continuousAt_const.mul (continuousAt_const.sub
      (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith [hy.1]))))).continuousWithinAt)
    (fun y hy ↦ by
      have h := (Real.hasDerivAt_rpow_const (p := -w.re) (Or.inl (by linarith [hy.1] :
        y ≠ 0))).const_sub (n ^ (-w.re)) |>.const_mul (‖w‖ / w.re)
      refine (h.congr_deriv ?_).hasDerivWithinAt
      field_simp)
    (fun y hy ↦ (norm_neg_mul_ofReal_cpow w (by linarith [hy.1] : 0 < y)).le)
    (Set.right_mem_Icc.mpr (by linarith))
  rw [norm_sub_rev]
  simpa using key

/-- **Lipschitz bound for consecutive complex powers.** For `Re w ≥ 0` and `n ≥ 1`,
`‖n^{-w} - (n + 1)^{-w}‖ ≤ ‖w‖ n^{-Re w - 1}`. -/
theorem norm_ofReal_cpow_neg_sub_succ_le' {w : ℂ} (hw : 0 ≤ w.re) {n : ℝ} (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-w) - ((n + 1 : ℝ) : ℂ) ^ (-w)‖ ≤ ‖w‖ * n ^ (-w.re - 1) := by
  have key := norm_image_sub_le_of_norm_deriv_right_le_segment
    (f := fun y : ℝ ↦ (y : ℂ) ^ (-w))
    (f' := fun y ↦ -w * (y : ℂ) ^ (-w - 1)) (C := ‖w‖ * n ^ (-w.re - 1))
    (a := n) (b := n + 1)
    (fun y hy ↦ (hasDerivAt_ofReal_cpow_neg w (by linarith [hy.1] : 0 < y)).continuousAt
      |>.continuousWithinAt)
    (fun y hy ↦ (hasDerivAt_ofReal_cpow_neg w (by linarith [hy.1] : 0 < y)).hasDerivWithinAt)
    (fun y hy ↦ by
      rw [norm_neg_mul_ofReal_cpow w (by linarith [hy.1] : 0 < y)]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by linarith) hy.1 (by linarith)) (norm_nonneg _))
    (n + 1) (Set.right_mem_Icc.mpr (by linarith))
  rw [norm_sub_rev]
  simpa using key

/-- `norm_ofReal_cpow_neg_sub_succ_le` at a natural number. -/
theorem norm_natCast_cpow_neg_sub_succ_le {w : ℂ} (hw : 0 < w.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-w) - ((n + 1 : ℕ) : ℂ) ^ (-w)‖ ≤
      ‖w‖ / w.re * ((n : ℝ) ^ (-w.re) - ((n + 1 : ℕ) : ℝ) ^ (-w.re)) := by
  have := norm_ofReal_cpow_neg_sub_succ_le hw (n := n) (by exact_mod_cast hn)
  push_cast at this ⊢
  exact this

/-- `norm_ofReal_cpow_neg_sub_succ_le'` at a natural number. -/
theorem norm_natCast_cpow_neg_sub_succ_le' {w : ℂ} (hw : 0 ≤ w.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-w) - ((n + 1 : ℕ) : ℂ) ^ (-w)‖ ≤ ‖w‖ * (n : ℝ) ^ (-w.re - 1) := by
  have := norm_ofReal_cpow_neg_sub_succ_le' hw (n := n) (by exact_mod_cast hn)
  push_cast at this ⊢
  exact this

end Complex

namespace ZMod

variable {q : ℕ} [NeZero q]

/-- The L-function of a finite sum of functions on `ZMod q` is the sum of their L-functions. -/
theorem LFunction_sum {ι : Type*} (t : Finset ι) (Φ : ι → ZMod q → ℂ) (s : ℂ) :
    LFunction (fun j ↦ ∑ i ∈ t, Φ i j) s = ∑ i ∈ t, LFunction (Φ i) s := by
  simp only [LFunction, sum_mul, mul_sum]
  exact sum_comm

/-- **`L(s, Φ)` from a truncated sum, `Re s > 0`.** Let `Φ : ZMod q → ℂ` have total sum `0`,
and suppose `‖∑_{1 ≤ n ≤ N} Φ n‖ ≤ B` for every `N`. Then for `Re s > 0` and `x ≥ 1`,
`‖L(s, Φ) - ∑_{1 ≤ n ≤ x} Φ n / n ^ s‖ ≤ 2 B (‖s‖ / Re s) x ^ (-Re s)`. -/
theorem norm_LFunction_sub_sum_Icc_le {Φ : ZMod q → ℂ} (hΦ : ∑ j, Φ j = 0) {B : ℝ}
    (hB : ∀ N : ℕ, ‖∑ n ∈ Icc 1 N, Φ n‖ ≤ B) {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 1 ≤ x) :
    ‖LFunction Φ s - ∑ n ∈ Icc 1 ⌊x⌋₊, Φ n / (n : ℂ) ^ s‖ ≤
      2 * B * (‖s‖ / s.re) * x ^ (-s.re) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  set m := ⌊x⌋₊ with hm
  obtain ⟨A, hA⟩ : ∃ A : ℕ → ℂ, ∀ N, A N = ∑ n ∈ Icc 1 N, Φ n := ⟨_, fun _ ↦ rfl⟩
  have hAb : ∀ N, ‖A N‖ ≤ B := fun N ↦ (hA N) ▸ hB N
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℂ → ℂ, ∀ k w, F k w = A (m + k + 1) *
      (((m + k + 1 : ℕ) : ℂ) ^ (-w) - ((m + k + 1 + 1 : ℕ) : ℂ) ^ (-w)) :=
    ⟨_, fun _ _ ↦ rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℕ → ℝ, ∀ w k, G w k = ((m + k + 1 : ℕ) : ℝ) ^ (-w.re) :=
    ⟨_, fun _ _ ↦ rfl⟩
  have hG0 : ∀ w k, 0 ≤ G w k := fun w k ↦ by rw [hG]; positivity
  have hFle : ∀ w : ℂ, 0 < w.re → ∀ k, ‖F k w‖ ≤ B * (‖w‖ / w.re) * (G w k - G w (k + 1)) := by
    intro w hw k
    rw [hF, norm_mul, hG, hG]
    have h1 := Complex.norm_natCast_cpow_neg_sub_succ_le hw (n := m + k + 1) (by omega)
    calc _ ≤ B * (‖w‖ / w.re * (((m + k + 1 : ℕ) : ℝ) ^ (-w.re) -
          ((m + k + 1 + 1 : ℕ) : ℝ) ^ (-w.re))) :=
          mul_le_mul (hAb _) h1 (norm_nonneg _) hB0
      _ = _ := by rw [mul_assoc]; rfl
  have hFsum : ∀ w : ℂ, 0 < w.re → ∀ J, ∑ k ∈ range J, ‖F k w‖ ≤ B * (‖w‖ / w.re) * G w 0 := by
    intro w hw J
    calc _ ≤ ∑ k ∈ range J, B * (‖w‖ / w.re) * (G w k - G w (k + 1)) :=
          sum_le_sum fun k _ ↦ hFle w hw k
      _ = B * (‖w‖ / w.re) * (G w 0 - G w J) := by rw [← mul_sum, sum_range_sub']
      _ ≤ _ := by
          have : 0 ≤ B * (‖w‖ / w.re) := mul_nonneg hB0 (div_nonneg (norm_nonneg _) hw.le)
          have := hG0 w J
          nlinarith
  have hFsummable : ∀ w : ℂ, 0 < w.re → Summable fun k ↦ ‖F k w‖ :=
    fun w hw ↦ summable_of_sum_range_le (fun _ ↦ norm_nonneg _) (hFsum w hw)
  obtain ⟨T, hT⟩ : ∃ T : ℂ → ℂ, ∀ w, T w = -A m * ((m + 1 : ℕ) : ℂ) ^ (-w) + ∑' k, F k w :=
    ⟨_, fun _ ↦ rfl⟩
  -- The bound on `T`.
  have hTb : ‖T s‖ ≤ B * G s 0 + B * (‖s‖ / s.re) * G s 0 := by
    rw [hT]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, norm_neg, Complex.norm_natCast_cpow_of_pos (by omega), hG]
      simp only [Complex.neg_re]
      exact mul_le_mul_of_nonneg_right (hAb m) (by positivity)
    · refine (norm_tsum_le_tsum_norm (hFsummable s hs)).trans ?_
      exact Real.tsum_le_of_sum_range_le (fun _ ↦ norm_nonneg _) (hFsum s hs)
  -- `T` is holomorphic on the right half-plane.
  have hTd : DifferentiableOn ℂ T {w | 0 < w.re} := by
    intro s₀ hs₀
    simp only [Set.mem_ofPred_eq] at hs₀
    set V : Set ℂ := {w | s₀.re / 2 < w.re} ∩ Metric.ball 0 (‖s₀‖ + 1)
    have hVo : IsOpen V :=
      (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
    have hs₀V : s₀ ∈ V := ⟨by simp only [Set.mem_ofPred_eq]; linarith, by simp⟩
    have hsumd : DifferentiableOn ℂ (fun w ↦ ∑' k, F k w) V := by
      refine Complex.differentiableOn_tsum_of_summable_norm
        (u := fun k ↦ B * ((‖s₀‖ + 1) * ((m + k + 1 : ℕ) : ℝ) ^ (-(s₀.re / 2) - 1)))
        ?_ ?_ hVo ?_
      · refine Summable.mul_left _ (Summable.mul_left _ ?_)
        have h := (summable_nat_add_iff (m + 1)).mpr
          (Real.summable_nat_rpow.mpr (by linarith : -(s₀.re / 2) - 1 < -1))
        refine h.congr fun k ↦ ?_
        congr 2
        omega
      · intro k w _
        rw [show F k = fun w ↦ A (m + k + 1) *
          (((m + k + 1 : ℕ) : ℂ) ^ (-w) - ((m + k + 1 + 1 : ℕ) : ℂ) ^ (-w)) from funext (hF k)]
        have h1 : ((m + k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : m + k + 1 ≠ 0)
        have h2 : ((m + k + 1 + 1 : ℕ) : ℂ) ≠ 0 := by
          exact_mod_cast (by omega : m + k + 1 + 1 ≠ 0)
        exact (((differentiableAt_id.neg.const_cpow (Or.inl h1)).sub
          (differentiableAt_id.neg.const_cpow (Or.inl h2))).const_mul _).differentiableWithinAt
      · intro k w hw
        obtain ⟨hw1, hw2⟩ := hw
        simp only [Set.mem_ofPred_eq] at hw1
        simp only [Metric.mem_ball, dist_zero_right] at hw2
        rw [hF, norm_mul]
        have h1 := Complex.norm_natCast_cpow_neg_sub_succ_le' (w := w) (by linarith)
          (n := m + k + 1) (by omega)
        have hn1 : (1 : ℝ) ≤ ((m + k + 1 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : 1 ≤ m + k + 1)
        have h3 : ((m + k + 1 : ℕ) : ℝ) ^ (-w.re - 1) ≤
            ((m + k + 1 : ℕ) : ℝ) ^ (-(s₀.re / 2) - 1) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        refine mul_le_mul (hAb _) (h1.trans ?_) (norm_nonneg _) hB0
        exact mul_le_mul hw2.le h3 (by positivity) (by positivity)
    have hfirst : DifferentiableAt ℂ (fun w ↦ -A m * ((m + 1 : ℕ) : ℂ) ^ (-w)) s₀ :=
      (differentiableAt_id.neg.const_cpow
        (Or.inl (by exact_mod_cast (by omega : m + 1 ≠ 0)))).const_mul _
    have he : T = fun w ↦ -A m * ((m + 1 : ℕ) : ℂ) ^ (-w) + ∑' k, F k w := funext hT
    rw [he]
    exact (hfirst.add (hsumd.differentiableAt (hVo.mem_nhds hs₀V))).differentiableWithinAt
  -- Abel summation for the partial sums.
  have hsummand : ∀ (w : ℂ) (n : ℕ), Φ n / (n : ℂ) ^ w = Φ n * (n : ℂ) ^ (-w) := by
    intro w n; rw [Complex.cpow_neg, div_eq_mul_inv]
  have habel : ∀ (w : ℂ) (J : ℕ), ∑ n ∈ Icc 1 (m + J), Φ n / (n : ℂ) ^ w =
      ∑ n ∈ Icc 1 m, Φ n / (n : ℂ) ^ w - A m * ((m + 1 : ℕ) : ℂ) ^ (-w)
        + A (m + J) * ((m + J + 1 : ℕ) : ℂ) ^ (-w) + ∑ k ∈ range J, F k w := by
    intro w J
    induction J with
    | zero => simp
    | succ J ih =>
      rw [← add_assoc, sum_Icc_succ_top (by omega), ih, sum_range_succ, hF,
        hA (m + J + 1), sum_Icc_succ_top (by omega), ← hA, hsummand]
      ring
  -- Agreement on `Re w > 1`.
  have hagree : ∀ w : ℂ, 1 < w.re →
      LFunction Φ w = ∑ n ∈ Icc 1 m, Φ n / (n : ℂ) ^ w + T w := by
    intro w hw
    have hw0 : 0 < w.re := by linarith
    rw [LFunction_eq_LSeries Φ hw]
    have hsum := (LSeriesSummable_of_one_lt_re Φ hw).hasSum
    have h2 : Tendsto (fun J : ℕ ↦ ∑ n ∈ Icc 1 (m + J), Φ n / (n : ℂ) ^ w)
        atTop (𝓝 (LSeries (fun n ↦ Φ n) w)) := by
      have := hsum.tendsto_sum_nat.comp (tendsto_add_atTop_nat (m + 1))
      refine this.congr fun J ↦ ?_
      simp only [Function.comp]
      rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega), LSeries.term_zero, zero_add]
      refine sum_congr (by ext; simp; omega) fun n hn ↦ ?_
      rw [LSeries.term_of_ne_zero (by simp at hn; omega)]
    have hb : Tendsto (fun J : ℕ ↦ A (m + J) * ((m + J + 1 : ℕ) : ℂ) ^ (-w)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hc : Tendsto (fun J : ℕ ↦ ((m + J + 1 : ℕ) : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp
          (tendsto_atTop_atTop.mpr fun b ↦ ⟨b, fun J hJ ↦ by omega⟩)
      have hlim : Tendsto (fun J : ℕ ↦ B * ((m + J + 1 : ℕ) : ℝ) ^ (-w.re)) atTop (𝓝 0) := by
        simpa using ((tendsto_rpow_neg_atTop hw0).comp hc).const_mul B
      refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun J ↦ ?_) hlim
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
      simp only [Complex.neg_re]
      exact mul_le_mul_of_nonneg_right (hAb _) (by positivity)
    have hTs := ((hFsummable w hw0).of_norm).hasSum.tendsto_sum_nat
    have h3 := ((tendsto_const_nhds (x := ∑ n ∈ Icc 1 m, Φ n / (n : ℂ) ^ w -
      A m * ((m + 1 : ℕ) : ℂ) ^ (-w))).add hb).add hTs
    rw [add_zero] at h3
    have h3' : Tendsto (fun J : ℕ ↦ ∑ n ∈ Icc 1 (m + J), Φ n / (n : ℂ) ^ w)
        atTop (𝓝 (∑ n ∈ Icc 1 m, Φ n / (n : ℂ) ^ w + T w)) := by
      convert h3 using 1
      · funext J; exact habel w J
      · rw [hT]; ring_nf
    exact tendsto_nhds_unique h2 h3'
  -- The identity theorem.
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hSd : Differentiable ℂ (fun w : ℂ ↦ ∑ n ∈ Icc 1 m, Φ n / (n : ℂ) ^ w) := by
    intro w
    simp_rw [hsummand]
    refine DifferentiableAt.fun_sum fun n hn ↦ ?_
    have hn0 : (n : ℂ) ≠ 0 := by simp at hn; exact_mod_cast (by omega : n ≠ 0)
    exact (differentiableAt_id.neg.const_cpow (Or.inl hn0)).const_mul _
  have hH : DifferentiableOn ℂ (fun w ↦ LFunction Φ w -
      (∑ n ∈ Icc 1 m, Φ n / (n : ℂ) ^ w + T w)) {w | 0 < w.re} :=
    (differentiable_LFunction_of_sum_zero hΦ).differentiableOn.sub
      (hSd.differentiableOn.add hTd)
  have hzero := (hH.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_re_gt 0).isPreconnected (z₀ := 2) (by simp)
    (Filter.eventually_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {w : ℂ | 1 < w.re} by simp)) fun w hw ↦ by
        simp only [Pi.zero_apply]
        rw [hagree w hw, sub_self])
  have hEq := hzero (show s ∈ {w : ℂ | 0 < w.re} from hs)
  simp only [Pi.zero_apply] at hEq
  have hdiff : LFunction Φ s - ∑ n ∈ Icc 1 m, Φ n / (n : ℂ) ^ s = T s := by
    linear_combination hEq
  rw [hdiff]
  have hxm : x < (m : ℝ) + 1 := by rw [hm]; exact Nat.lt_floor_add_one x
  have hG1 : G s 0 ≤ x ^ (-s.re) := by
    rw [hG]
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by push_cast; linarith) (by linarith)
  have hr : 1 ≤ ‖s‖ / s.re := by
    rw [le_div_iff₀ hs, one_mul]; exact Complex.re_le_norm s
  have hG00 := hG0 s 0
  have e1 : B * G s 0 ≤ B * (‖s‖ / s.re) * G s 0 := by
    have := mul_nonneg hB0 hG00
    nlinarith
  have e2 : B * (‖s‖ / s.re) * G s 0 ≤ B * (‖s‖ / s.re) * x ^ (-s.re) :=
    mul_le_mul_of_nonneg_left hG1 (by positivity)
  linarith

end ZMod

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

/-- **`L(s, χ)` from a short character sum, `Re s > 0`.** For a nontrivial Dirichlet character
`χ` modulo `q`, `Re s > 0` and `x ≥ 1`,
`‖L(s, χ) - ∑_{1 ≤ n ≤ x} χ n / n ^ s‖ ≤ 4 ‖s‖ √q (1 + log q) / (Re s · x ^ Re s)`. -/
theorem norm_LFunction_sub_sum_Icc_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) {x : ℝ} (hx : 1 ≤ x) :
    ‖LFunction χ s - ∑ n ∈ Icc 1 ⌊x⌋₊, χ n / (n : ℂ) ^ s‖ ≤
      4 * ‖s‖ * Real.sqrt q * (1 + Real.log q) / (s.re * x ^ s.re) := by
  refine (ZMod.norm_LFunction_sub_sum_Icc_le (χ.sum_eq_zero_of_ne_one hχ) (norm_sum_Icc_le hχ)
    hs hx).trans (le_of_eq ?_)
  rw [Real.rpow_neg (by linarith)]
  field_simp
  ring

/-- **`L(1, χ)` from a short character sum.** For a nontrivial Dirichlet character `χ` modulo
`q` and `x ≥ 1`, `‖L(1, χ) - ∑_{1 ≤ n ≤ x} χ n / n‖ ≤ 4 √q (1 + log q) / x`. -/
theorem norm_LFunction_one_sub_sum_Icc_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {x : ℝ}
    (hx : 1 ≤ x) :
    ‖LFunction χ 1 - ∑ n ∈ Icc 1 ⌊x⌋₊, χ n / (n : ℂ)‖ ≤
      4 * Real.sqrt q * (1 + Real.log q) / x := by
  have h := norm_LFunction_sub_sum_Icc_le hχ (s := 1) (by simp) hx
  simpa only [Complex.cpow_one, Complex.one_re, norm_one, mul_one, one_mul, Real.rpow_one]
    using h

open scoped Classical in
/-- The sum `∑_{χ ≠ 1} χ` of the nontrivial Dirichlet characters modulo `q`. -/
private noncomputable def sumNontrivial (q : ℕ) [NeZero q] (z : ZMod q) : ℂ :=
  ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q), χ z

open scoped Classical in
/-- The common estimate behind the averages of `L(s, χ)` over nontrivial characters: with the
truncation point `x = q`,
`‖∑_{χ ≠ 1} L(s, χ) - φ(q) + ∑_{n ≤ q} χ₀ n / n ^ s‖ ≤ 4 (‖s‖ / Re s) q ^ (1 - Re s)`. -/
private lemma norm_sum_LFunction_sub_totient_add_le {s : ℂ} (hs : 0 < s.re) :
    ‖(∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q), LFunction χ s) - (q.totient : ℂ) +
        ∑ n ∈ Icc 1 q, (1 : DirichletCharacter ℂ q) n / (n : ℂ) ^ s‖ ≤
      4 * (‖s‖ / s.re) * (q : ℝ) ^ (1 - s.re) := by
  set g := sumNontrivial q
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq0
  have hgform : ∀ z, g z = (if z = 1 then (q.totient : ℂ) else 0) -
      (1 : DirichletCharacter ℂ q) z := by
    intro z
    simp only [g, sumNontrivial]
    rw [sum_erase_eq_sub (mem_univ _), sum_characters_eq]
  have hgsum : ∑ z, g z = 0 := by
    simp only [g, sumNontrivial]
    rw [sum_comm]
    exact sum_eq_zero fun χ hχ ↦ MulChar.sum_eq_zero_of_ne_one (ne_of_mem_erase hχ)
  have hgabs : ∑ z, ‖g z‖ ≤ 2 * q := by
    calc ∑ z, ‖g z‖ ≤ ∑ z : ZMod q, (‖(if z = 1 then (q.totient : ℂ) else 0)‖ + 1) :=
          sum_le_sum fun z _ ↦ by
            rw [hgform]
            exact (norm_sub_le _ _).trans (by gcongr; exact norm_le_one _ _)
      _ = q.totient + q := by
          rw [sum_add_distrib]
          simp [apply_ite]
      _ ≤ 2 * q := by
          have : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
          linarith
  have hB : ∀ N : ℕ, ‖∑ n ∈ Icc 1 N, g n‖ ≤ 2 * q := by
    intro N
    have : Icc 1 N = Ico 1 (N + 1) := by ext; simp only [mem_Icc, mem_Ico]; omega
    rw [this]
    exact (ZMod.norm_sum_Ico_le_of_sum_eq_zero hgsum _ _).trans hgabs
  have hL : ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q), LFunction χ s =
      ZMod.LFunction g s := by
    simp only [g, LFunction]
    exact (ZMod.LFunction_sum _ (fun χ : DirichletCharacter ℂ q ↦ (χ : ZMod q → ℂ)) s).symm
  have habel := ZMod.norm_LFunction_sub_sum_Icc_le hgsum hB hs hqR
  rw [Nat.floor_natCast] at habel
  have hmain : ∑ n ∈ Icc 1 q, g n / (n : ℂ) ^ s = (q.totient : ℂ) -
      ∑ n ∈ Icc 1 q, (1 : DirichletCharacter ℂ q) n / (n : ℂ) ^ s := by
    simp only [hgform, sub_div, sum_sub_distrib]
    congr 1
    rw [sum_eq_single 1]
    · simp
    · intro n hn hne
      rw [ite_eq_right, zero_div]
      intro hn1
      have h := (ZMod.natCast_eq_natCast_iff' n 1 q).mp (by simpa using hn1)
      obtain ⟨hn1', hnq⟩ := mem_Icc.mp hn
      rcases hnq.lt_or_eq with hlt | heq
      · rw [Nat.mod_eq_of_lt hlt] at h
        rcases Nat.lt_or_ge 1 q with h1q | h1q
        · rw [Nat.mod_eq_of_lt h1q] at h; exact hne h
        · omega
      · rw [heq, Nat.mod_self] at h
        rcases Nat.lt_or_ge 1 q with h1q | h1q
        · rw [Nat.mod_eq_of_lt h1q] at h; omega
        · omega
    · intro h; exact absurd (mem_Icc.mpr ⟨le_rfl, hq0⟩) h
  have e : (∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q), LFunction χ s) - (q.totient : ℂ) +
      ∑ n ∈ Icc 1 q, (1 : DirichletCharacter ℂ q) n / (n : ℂ) ^ s =
      ZMod.LFunction g s - ∑ n ∈ Icc 1 q, g n / (n : ℂ) ^ s := by
    rw [hL, hmain]; ring
  rw [e]
  refine habel.trans (le_of_eq ?_)
  rw [sub_eq_add_neg, Real.rpow_add (by linarith), Real.rpow_one]
  ring

open scoped Classical in
/-- **The sum of `L(1, χ)` over the nontrivial characters.** For every modulus `q`,
`‖∑_{χ ≠ 1} L(1, χ) - φ(q)‖ ≤ 5 + log q`. In particular
`∑_{χ ≠ 1} L(1, χ) = φ(q) + O(log q)`. -/
theorem norm_sum_LFunction_one_sub_totient_le :
    ‖(∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q), LFunction χ 1) - (q.totient : ℂ)‖ ≤
      5 + Real.log q := by
  have h := norm_sum_LFunction_sub_totient_add_le (q := q) (s := 1) (by simp)
  simp only [Complex.one_re, norm_one, div_one, sub_self, Real.rpow_zero, mul_one,
    Complex.cpow_one] at h
  have hharm : ‖∑ n ∈ Icc 1 q, (1 : DirichletCharacter ℂ q) n / (n : ℂ)‖ ≤ 1 + Real.log q := by
    calc _ ≤ ∑ n ∈ Icc 1 q, ‖(1 : DirichletCharacter ℂ q) n / (n : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Icc 1 q, ((n : ℝ))⁻¹ := by
          refine sum_le_sum fun n hn ↦ ?_
          rw [norm_div, Complex.norm_natCast, div_eq_mul_inv]
          have : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
          calc _ ≤ 1 * (n : ℝ)⁻¹ := by gcongr; exact norm_le_one _ _
            _ = _ := one_mul _
      _ = (harmonic q : ℝ) := by rw [harmonic_eq_sum_Icc]; push_cast; rfl
      _ ≤ 1 + Real.log q := harmonic_le_one_add_log q
  have e : (∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q), LFunction χ 1) - (q.totient : ℂ) =
      ((∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q), LFunction χ 1) - (q.totient : ℂ) +
        ∑ n ∈ Icc 1 q, (1 : DirichletCharacter ℂ q) n / (n : ℂ)) -
      ∑ n ∈ Icc 1 q, (1 : DirichletCharacter ℂ q) n / (n : ℂ) := by ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  linarith

/-- `∑_{1 ≤ n ≤ N} n ^ (-3/2) ≤ 3`. -/
private lemma sum_Icc_rpow_neg_three_halves_le (N : ℕ) :
    ∑ n ∈ Icc 1 N, (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 3 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hanti : AntitoneOn (fun t : ℝ ↦ t ^ (-(3 / 2 : ℝ))) (Set.Icc (1 : ℝ) (1 + M)) :=
    fun x hx y _ hxy ↦ Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by norm_num)
  have hsum := hanti.sum_le_integral
  have hint : ∫ x in (1 : ℝ)..1 + M, x ^ (-(3 / 2 : ℝ)) ≤ 2 := by
    rw [integral_rpow (Or.inr ⟨by norm_num, fun h ↦ by
      rw [Set.mem_uIcc] at h
      rcases h with h | h <;> linarith [h.1, h.2, (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]⟩)]
    have hpos : 0 ≤ (1 + (M : ℝ)) ^ (-(3 / 2 : ℝ) + 1) := by positivity
    norm_num at hpos ⊢
    linarith
  have hI : Icc 1 (M + 1) = Ico 1 (M + 2) := by ext; simp only [mem_Icc, mem_Ico]; omega
  rw [hI, sum_Ico_eq_sum_range, show M + 2 - 1 = M + 1 by omega, sum_range_succ']
  have hre : ∑ i ∈ range M, (((1 + (i + 1) : ℕ) : ℝ)) ^ (-(3 / 2 : ℝ)) =
      ∑ i ∈ range M, (1 + ((i + 1 : ℕ) : ℝ)) ^ (-(3 / 2 : ℝ)) := by
    refine sum_congr rfl fun i _ ↦ ?_
    push_cast
    ring_nf
  rw [hre]
  simp only [add_zero, Nat.cast_one, Real.one_rpow]
  linarith

open scoped Classical in
/-- **The sum of `L(σ, χ)` over the nontrivial characters.** For `0 < σ ≤ 3/2` and every
modulus `q`, `‖∑_{χ ≠ 1} L(σ, χ) - φ(q)‖ ≤ 7 q ^ (3/2 - σ)`. -/
theorem norm_sum_LFunction_sub_totient_le {σ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ ≤ 3 / 2) :
    ‖(∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q), LFunction χ σ) - (q.totient : ℂ)‖ ≤
      7 * (q : ℝ) ^ (3 / 2 - σ) := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq0
  have h := norm_sum_LFunction_sub_totient_add_le (q := q) (s := σ) (by simpa using hσ₀)
  simp only [Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ₀,
    div_self hσ₀.ne'] at h
  have h1 : (q : ℝ) ^ (1 - σ) ≤ (q : ℝ) ^ (3 / 2 - σ) :=
    Real.rpow_le_rpow_of_exponent_le hqR (by linarith)
  have hrem : ‖∑ n ∈ Icc 1 q, (1 : DirichletCharacter ℂ q) n / (n : ℂ) ^ (σ : ℂ)‖ ≤
      3 * (q : ℝ) ^ (3 / 2 - σ) := by
    calc _ ≤ ∑ n ∈ Icc 1 q, ‖(1 : DirichletCharacter ℂ q) n / (n : ℂ) ^ (σ : ℂ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Icc 1 q, (q : ℝ) ^ (3 / 2 - σ) * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
          refine sum_le_sum fun n hnI ↦ ?_
          have hn : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hnI).1
          have hnq : (n : ℝ) ≤ q := by exact_mod_cast (mem_Icc.mp hnI).2
          rw [norm_div, Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hn),
            Complex.ofReal_re]
          calc _ ≤ 1 / (n : ℝ) ^ σ := by gcongr; exact norm_le_one _ _
            _ = (n : ℝ) ^ (3 / 2 - σ) * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
                rw [← Real.rpow_add hn, one_div, ← Real.rpow_neg hn.le]; ring_nf
            _ ≤ _ := by gcongr
      _ = (q : ℝ) ^ (3 / 2 - σ) * ∑ n ∈ Icc 1 q, (n : ℝ) ^ (-(3 / 2 : ℝ)) := by rw [mul_sum]
      _ ≤ (q : ℝ) ^ (3 / 2 - σ) * 3 :=
          mul_le_mul_of_nonneg_left (sum_Icc_rpow_neg_three_halves_le q) (by positivity)
      _ = _ := mul_comm _ _
  have e : (∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q), LFunction χ σ) - (q.totient : ℂ) =
      ((∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q), LFunction χ σ) - (q.totient : ℂ) +
        ∑ n ∈ Icc 1 q, (1 : DirichletCharacter ℂ q) n / (n : ℂ) ^ (σ : ℂ)) -
      ∑ n ∈ Icc 1 q, (1 : DirichletCharacter ℂ q) n / (n : ℂ) ^ (σ : ℂ) := by ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  linarith

end DirichletCharacter
