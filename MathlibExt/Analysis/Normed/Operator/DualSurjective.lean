/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.Normed.Operator.DualApproximatePreimage

/-!
# Exact Banach preimages from a dual lower bound

Let `E` be a complete complex normed space, `F` a complex normed space and `B : E →L[ℂ] F`. If
`‖G‖≤‖G∘B‖` for every continuous functional `G ∈ F*`, then every `y ∈ F` has a preimage `x ∈ E`
with `Bx=y` and `‖x‖≤5‖y‖`.

Thus `B` is surjective. Completeness of `F` is not required, and the zero target and zero vector
cases are included.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set
open scoped Topology BigOperators

namespace ContinuousLinearMap

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Exact preimage with a Banach norm bound.** Let `E` be a complete complex normed space,
`F` a complex normed space and `B : E →L[ℂ] F` satisfy `‖G‖≤‖G∘B‖` for every `G ∈ F*`. For
each `y ∈ F` there exists `x ∈ E` with `Bx=y` and `‖x‖≤5‖y‖`. The target may be
incomplete. -/
theorem exists_preimage_norm_le_of_dual_lower_bound (B : E →L[ℂ] F)
    (hdual : ∀ G : StrongDual ℂ F, ‖G‖ ≤ ‖G.comp B‖) (y : F) :
    ∃ x : E, B x = y ∧ ‖x‖ ≤ 5 * ‖y‖ := by
  classical
  choose g hg using fun z : F => B.exists_controlled_approx_preimage_of_dual_lower_bound hdual z
  let h (z : F) := z - B (g z)
  have hle (z : F) : ‖h z‖ ≤ (1 / 2 : ℝ) * ‖z‖ := by
    rw [← dist_eq_norm, dist_comm]
    exact (hg z).1
  have hnle (n : ℕ) : ‖h^[n] y‖ ≤ (1 / 2 : ℝ) ^ n * ‖y‖ := by
    induction n with
    | zero => simp only [Function.iterate_zero_apply, pow_zero, one_mul, le_refl]
    | succ n ih =>
      rw [Function.iterate_succ']
      apply (hle _).trans
      rw [pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left ih (by norm_num)
  let u (n : ℕ) : E := g (h^[n] y)
  have ule (n : ℕ) : ‖u n‖ ≤ (1 / 2 : ℝ) ^ n * (2 * ‖y‖) := by
    calc
      ‖u n‖ ≤ 2 * ‖h^[n] y‖ := (hg _).2
      _ ≤ 2 * ((1 / 2 : ℝ) ^ n * ‖y‖) := mul_le_mul_of_nonneg_left (hnle n) (by norm_num)
      _ = (1 / 2 : ℝ) ^ n * (2 * ‖y‖) := by ring
  have sn : Summable (fun n => ‖u n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg (u n)) ule
      (Summable.mul_right _ summable_geometric_two)
  have su : Summable u := sn.of_norm
  let x : E := ∑' n, u n
  have hnorm : ‖x‖ ≤ 5 * ‖y‖ := by
    calc
      ‖x‖ ≤ ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm sn
      _ ≤ ∑' n, (1 / 2 : ℝ) ^ n * (2 * ‖y‖) :=
        sn.tsum_le_tsum ule (Summable.mul_right _ summable_geometric_two)
      _ = (∑' n, (1 / 2 : ℝ) ^ n) * (2 * ‖y‖) := tsum_mul_right
      _ = 4 * ‖y‖ := by rw [tsum_geometric_two]; ring
      _ ≤ 5 * ‖y‖ := by nlinarith [norm_nonneg y]
  have hsum (n : ℕ) : B (∑ i ∈ Finset.range n, u i) = y - h^[n] y := by
    induction n with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, map_zero, Function.iterate_zero_apply, sub_self]
    | succ n ih =>
      rw [Finset.sum_range_succ, B.map_add, ih, Function.iterate_succ_apply', sub_add]
  have hsumLimit : Tendsto (fun n => ∑ i ∈ Finset.range n, u i) atTop (𝓝 x) :=
    su.hasSum.tendsto_sum_nat
  have himageLimit : Tendsto (fun n => B (∑ i ∈ Finset.range n, u i)) atTop (𝓝 (B x)) :=
    (B.continuous.tendsto x).comp hsumLimit
  have hresidual : Tendsto (fun n => h^[n] y) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    apply squeeze_zero (fun n => norm_nonneg (h^[n] y)) hnle
    have hpow := (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul
      (tendsto_const_nhds : Tendsto (fun _n : ℕ => ‖y‖) atTop _)
    simpa only [zero_mul] using hpow
  have htarget : Tendsto (fun n => y - h^[n] y) atTop (𝓝 y) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _n : ℕ => y) atTop _).sub hresidual
  rw [show (fun n => B (∑ i ∈ Finset.range n, u i)) = (fun n => y - h^[n] y) from funext hsum]
    at himageLimit
  exact ⟨x, tendsto_nhds_unique himageLimit htarget, hnorm⟩

/-- **Surjectivity from a lower bound on the dual map.** Let `E` be a complete complex normed
space, `F` a complex normed space and `B : E →L[ℂ] F`. If `‖G‖≤‖G∘B‖` for every continuous
complex-linear functional `G ∈ F*`, then `B` is surjective; no completeness of `F` is
assumed. -/
theorem surjective_of_dual_lower_bound (B : E →L[ℂ] F)
    (hdual : ∀ G : StrongDual ℂ F, ‖G‖ ≤ ‖G.comp B‖) : Function.Surjective B := by
  intro y
  obtain ⟨x, hxy, _hnorm⟩ := B.exists_preimage_norm_le_of_dual_lower_bound hdual y
  exact ⟨x, hxy⟩

end

end ContinuousLinearMap
