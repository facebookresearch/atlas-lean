/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.Basic

@[expose] public section

/-! # Projected online gradient descent

Zinkevich's regret bound for projected online gradient descent with a
nonexpansive projection and convex round costs (through their
subgradient inequality): the regret against any comparator fixed by
the projection is at most `‖x0 - xstar‖² / (2η) + (η/2) ∑ ‖g t‖²`.
This file covers roadmap package ML-13 of the Atlas TCS canon roadmap.

Source: M. Zinkevich, "Online convex programming and generalized
infinitesimal gradient ascent", ICML 2003.
-/

open Finset

/-- Projected online gradient descent iterates: `x (t + 1)` projects
the gradient step from `x t` back with `proj`. Here `g t x` is the
subgradient of the round-`t` cost at `x`, and `η` is the step size. -/
noncomputable def ogdIter {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (proj : E → E) (g : ℕ → E → E) (η : ℝ) (x0 : E) : ℕ → E
  | 0 => x0
  | t + 1 => proj (ogdIter proj g η x0 t - η • g t (ogdIter proj g η x0 t))

/-- Zinkevich's regret bound for projected online gradient descent:
with a nonexpansive projection fixing the comparator `xstar`, and
subgradients satisfying the convexity inequality, the regret against
`xstar` over `T` rounds is at most
`‖x0 - xstar‖² / (2η) + (η / 2) ∑ ‖g t (x t)‖²`. -/
theorem ogd_regret {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {proj : E → E} {f : ℕ → E → ℝ} {g : ℕ → E → E} {η : ℝ} (hη : 0 < η)
    (hproj : ∀ u v, ‖proj u - proj v‖ ≤ ‖u - v‖)
    (xstar : E) (hprojstar : proj xstar = xstar)
    (hsub : ∀ (t : ℕ) (x : E), f t x + @inner ℝ E _ (g t x) (xstar - x) ≤ f t xstar)
    (x0 : E) (T : ℕ) :
    ∑ t ∈ Finset.range T, (f t (ogdIter proj g η x0 t) - f t xstar) ≤
      ‖x0 - xstar‖ ^ 2 / (2 * η) +
        (η / 2) * ∑ t ∈ Finset.range T, ‖g t (ogdIter proj g η x0 t)‖ ^ 2 := by
  have hstep : ∀ t : ℕ, ‖ogdIter proj g η x0 (t + 1) - xstar‖ ^ 2 ≤
      ‖ogdIter proj g η x0 t - xstar‖ ^ 2
        - 2 * η * inner ℝ (g t (ogdIter proj g η x0 t)) (ogdIter proj g η x0 t - xstar)
        + η ^ 2 * ‖g t (ogdIter proj g η x0 t)‖ ^ 2 := by
    intro t
    have hrec : ogdIter proj g η x0 (t + 1)
        = proj (ogdIter proj g η x0 t - η • g t (ogdIter proj g η x0 t)) := rfl
    have hnonexp : ‖ogdIter proj g η x0 (t + 1) - xstar‖
        ≤ ‖(ogdIter proj g η x0 t - η • g t (ogdIter proj g η x0 t)) - xstar‖ := by
      calc ‖ogdIter proj g η x0 (t + 1) - xstar‖
          = ‖proj (ogdIter proj g η x0 t - η • g t (ogdIter proj g η x0 t))
            - proj xstar‖ := by rw [hrec, hprojstar]
        _ ≤ ‖(ogdIter proj g η x0 t - η • g t (ogdIter proj g η x0 t)) - xstar‖ :=
            hproj _ _
    have hsq : ‖ogdIter proj g η x0 (t + 1) - xstar‖ ^ 2
        ≤ ‖(ogdIter proj g η x0 t - η • g t (ogdIter proj g η x0 t)) - xstar‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnonexp 2
    have hexpand : ‖(ogdIter proj g η x0 t - η • g t (ogdIter proj g η x0 t)) - xstar‖ ^ 2
        = ‖ogdIter proj g η x0 t - xstar‖ ^ 2
          - 2 * η * inner ℝ (g t (ogdIter proj g η x0 t)) (ogdIter proj g η x0 t - xstar)
          + η ^ 2 * ‖g t (ogdIter proj g η x0 t)‖ ^ 2 := by
      have hsub : (ogdIter proj g η x0 t - η • g t (ogdIter proj g η x0 t)) - xstar
          = (ogdIter proj g η x0 t - xstar) - η • g t (ogdIter proj g η x0 t) := by abel
      rw [hsub, norm_sub_sq_real, inner_smul_right,
        real_inner_comm (g t (ogdIter proj g η x0 t)) (ogdIter proj g η x0 t - xstar),
        norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      ring
    calc ‖ogdIter proj g η x0 (t + 1) - xstar‖ ^ 2
        ≤ ‖(ogdIter proj g η x0 t - η • g t (ogdIter proj g η x0 t)) - xstar‖ ^ 2 := hsq
      _ = _ := hexpand
  have hreg : ∀ t : ℕ, 2 * η * (f t (ogdIter proj g η x0 t) - f t xstar) ≤
      (‖ogdIter proj g η x0 t - xstar‖ ^ 2 - ‖ogdIter proj g η x0 (t + 1) - xstar‖ ^ 2)
        + η ^ 2 * ‖g t (ogdIter proj g η x0 t)‖ ^ 2 := by
    intro t
    have hI : f t (ogdIter proj g η x0 t) - f t xstar
        ≤ inner ℝ (g t (ogdIter proj g η x0 t)) (ogdIter proj g η x0 t - xstar) := by
      have h := hsub t (ogdIter proj g η x0 t)
      have hinner : inner ℝ (g t (ogdIter proj g η x0 t)) (xstar - ogdIter proj g η x0 t)
          = -inner ℝ (g t (ogdIter proj g η x0 t)) (ogdIter proj g η x0 t - xstar) := by
        have hneg : xstar - ogdIter proj g η x0 t
            = -(ogdIter proj g η x0 t - xstar) := by abel
        rw [hneg, inner_neg_right]
      rw [hinner] at h
      linarith
    have h2η : (0 : ℝ) ≤ 2 * η := by linarith [hη]
    have hmul := mul_le_mul_of_nonneg_left hI h2η
    have hs := hstep t
    linarith
  have htele : ∀ n : ℕ, ∑ t ∈ Finset.range n, (‖ogdIter proj g η x0 t - xstar‖ ^ 2
      - ‖ogdIter proj g η x0 (t + 1) - xstar‖ ^ 2)
      = ‖ogdIter proj g η x0 0 - xstar‖ ^ 2 - ‖ogdIter proj g η x0 n - xstar‖ ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  have hsum : (2 * η) * (∑ t ∈ Finset.range T, (f t (ogdIter proj g η x0 t) - f t xstar))
      ≤ (‖ogdIter proj g η x0 0 - xstar‖ ^ 2 - ‖ogdIter proj g η x0 T - xstar‖ ^ 2)
        + η ^ 2 * (∑ t ∈ Finset.range T, ‖g t (ogdIter proj g η x0 t)‖ ^ 2) := by
    have hle : ∑ t ∈ Finset.range T, (2 * η * (f t (ogdIter proj g η x0 t) - f t xstar))
        ≤ ∑ t ∈ Finset.range T, ((‖ogdIter proj g η x0 t - xstar‖ ^ 2
          - ‖ogdIter proj g η x0 (t + 1) - xstar‖ ^ 2)
          + η ^ 2 * ‖g t (ogdIter proj g η x0 t)‖ ^ 2) :=
      Finset.sum_le_sum (fun t _ => hreg t)
    have hLHS : ∑ t ∈ Finset.range T, (2 * η * (f t (ogdIter proj g η x0 t) - f t xstar))
        = (2 * η) * (∑ t ∈ Finset.range T, (f t (ogdIter proj g η x0 t) - f t xstar)) :=
      (Finset.mul_sum _ _ _).symm
    have hRHS : ∑ t ∈ Finset.range T, ((‖ogdIter proj g η x0 t - xstar‖ ^ 2
          - ‖ogdIter proj g η x0 (t + 1) - xstar‖ ^ 2)
          + η ^ 2 * ‖g t (ogdIter proj g η x0 t)‖ ^ 2)
        = (‖ogdIter proj g η x0 0 - xstar‖ ^ 2 - ‖ogdIter proj g η x0 T - xstar‖ ^ 2)
          + η ^ 2 * (∑ t ∈ Finset.range T, ‖g t (ogdIter proj g η x0 t)‖ ^ 2) := by
      rw [Finset.sum_add_distrib, htele T, ← Finset.mul_sum]
    rw [hLHS, hRHS] at hle
    exact hle
  have h0 : ogdIter proj g η x0 0 = x0 := rfl
  rw [h0] at hsum
  have hΦT : (0 : ℝ) ≤ ‖ogdIter proj g η x0 T - xstar‖ ^ 2 := by positivity
  have h2ηpos : (0 : ℝ) < 2 * η := by linarith [hη]
  have hηne : η ≠ 0 := ne_of_gt hη
  have h2ηne : (2 : ℝ) * η ≠ 0 := ne_of_gt h2ηpos
  have hRHS : ‖x0 - xstar‖ ^ 2 / (2 * η)
        + (η / 2) * (∑ t ∈ Finset.range T, ‖g t (ogdIter proj g η x0 t)‖ ^ 2)
      = (‖x0 - xstar‖ ^ 2 + η ^ 2 * (∑ t ∈ Finset.range T, ‖g t (ogdIter proj g η x0 t)‖ ^ 2))
        / (2 * η) := by
    field_simp
  rw [hRHS, le_div_iff₀ h2ηpos]
  have hcomm : (∑ t ∈ Finset.range T, (f t (ogdIter proj g η x0 t) - f t xstar)) * (2 * η)
      = (2 * η) * (∑ t ∈ Finset.range T, (f t (ogdIter proj g η x0 t) - f t xstar)) := by ring
  rw [hcomm]
  linarith [hsum, hΦT]
