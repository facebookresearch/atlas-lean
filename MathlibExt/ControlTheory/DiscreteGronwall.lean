/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.SpecialFunctions.Exp

import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.ODE.DiscreteGronwall
import Mathlib.Tactic.Ring

/-! # Discrete Grönwall bounds for perturbed iterations -/

open Finset
open scoped NNReal

namespace MetaMathlibExt

@[expose] public section

/-- **Discrete Grönwall error propagation for perturbed iterations.** Let `F` be `L`-Lipschitz
on a seminormed additive commutative group. If `x (k + 1) = F (x k)` and
`y (k + 1) = F (y k) + e k`, with
`‖e k‖ ≤ τ`, then `‖y k - x k‖` is bounded by the initial error times `L ^ k` plus `τ` times
the first `k` terms of the geometric series of ratio `L`. When `L = 1 + c * h` with `c, h ≥ 0`,
the error is at most `exp (c * k * h) * (‖y 0 - x 0‖ + k * τ)`. For `L < 1`, the geometric sum
is `(1 - L ^ k) / (1 - L)`.

The one-step discretization case is discussed in E. Süli, *Numerical Solution of Ordinary
Differential Equations*, in the estimate preceding (20) and the proof of (25). -/
theorem perturbed_iteration_gronwall {X : Type*} [SeminormedAddCommGroup X] {L : ℝ≥0}
    {F : X → X} (hF : LipschitzWith L F) {x y e : ℕ → X} {τ : ℝ}
    (hx : ∀ k, x (k + 1) = F (x k)) (hy : ∀ k, y (k + 1) = F (y k) + e k)
    (he : ∀ k, ‖e k‖ ≤ τ) (k : ℕ) :
    (‖y k - x k‖ ≤ (L : ℝ) ^ k * ‖y 0 - x 0‖ + τ * ∑ j ∈ range k, (L : ℝ) ^ j) ∧
    (∀ c h : ℝ, 0 ≤ c → 0 ≤ h → (L : ℝ) = 1 + c * h →
      ‖y k - x k‖ ≤ Real.exp (c * k * h) * (‖y 0 - x 0‖ + k * τ)) ∧
    ((L : ℝ) < 1 → ‖y k - x k‖ ≤ (L : ℝ) ^ k * ‖y 0 - x 0‖ +
      τ * ((1 - (L : ℝ) ^ k) / (1 - (L : ℝ)))) := by
  let u : ℕ → ℝ := fun j => ‖y j - x j‖
  have hstep (j : ℕ) : u (j + 1) ≤ (L : ℝ) * u j + τ := by
    have hdist : ‖F (y j) - F (x j)‖ ≤ (L : ℝ) * ‖y j - x j‖ := by
      simpa only [dist_eq_norm] using hF.dist_le_mul (y j) (x j)
    calc
      u (j + 1) = ‖(F (y j) - F (x j)) + e j‖ := by
        dsimp only [u]
        rw [hx, hy, add_sub_right_comm]
      _ ≤ ‖F (y j) - F (x j)‖ + ‖e j‖ := norm_add_le _ _
      _ ≤ (L : ℝ) * u j + τ := add_le_add hdist (he j)
  have hgeom : u k ≤ (L : ℝ) ^ k * u 0 + τ * ∑ j ∈ range k, (L : ℝ) ^ j := by
    have h := discrete_gronwall_prod_general (n₀ := 0) (u := u)
      (b := fun _ => τ) (c := fun _ => (L : ℝ)) (fun j _ => hstep j)
      (fun _ _ => L.coe_nonneg) (Nat.zero_le k)
    simp only [prod_const, Nat.card_Ico, Nat.Ico_zero_eq_range, card_range,
      ← mul_sum, Nat.sub_add_eq, Nat.sub_right_comm k _ 1] at h
    rw [sum_range_reflect (fun j => (L : ℝ) ^ j)] at h
    simpa only [mul_comm (u 0)] using h
  refine ⟨hgeom, ?_, ?_⟩
  · intro c h hc hh hL
    have ht : 0 ≤ τ := (norm_nonneg _).trans (he 0)
    have hstep' (j : ℕ) : u (j + 1) ≤ (1 + c * h) * u j + τ := by
      simpa only [hL] using hstep j
    have hbound := discrete_gronwall (n₀ := 0) (u := u) (b := fun _ => τ)
      (c := fun _ => c * h) (norm_nonneg _) (fun j _ => hstep' j)
      (fun _ _ => mul_nonneg hc hh) (fun _ _ => ht) (Nat.zero_le k)
    simp only [Nat.Ico_zero_eq_range, sum_const, card_range, nsmul_eq_mul] at hbound
    rw [show c * (k : ℝ) * h = (k : ℝ) * (c * h) by ring, mul_comm]
    exact hbound
  · intro hL
    have hsum : ∑ j ∈ range k, (L : ℝ) ^ j = (1 - (L : ℝ) ^ k) / (1 - (L : ℝ)) := by
      rw [geom_sum_eq hL.ne]
      simpa only [neg_sub] using
        (neg_div_neg_eq ((L : ℝ) ^ k - 1) ((L : ℝ) - 1)).symm
    rw [hsum] at hgeom
    exact hgeom

end

end MetaMathlibExt
