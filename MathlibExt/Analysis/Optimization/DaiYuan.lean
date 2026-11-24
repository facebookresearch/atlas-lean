/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Optimization.LineSearch
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The Dai–Yuan nonlinear conjugate gradient method

A nonlinear conjugate gradient method minimises a smooth `f` by
`x (k + 1) = x k + α k • d k`, `d 0 = -∇f(x 0)` and `d (k + 1) = -∇f(x (k + 1)) + β k • d k`.
Dai and Yuan choose `β k = ‖g (k + 1)‖² / ⟪d k, g (k + 1) - g k⟫` with `g k = ∇f(x k)`: the
Fletcher–Reeves numerator over the Hestenes–Stiefel denominator. This file proves

* the identity `⟪g (k + 1), d (k + 1)⟫ = β k ⟪g k, d k⟫` (equation (2.5) of the source);
* that every direction is a descent direction under the standard Wolfe conditions;
* the global convergence `liminf ‖g k‖ = 0` under the standard Wolfe conditions (Theorem 3.3).

Source: Y. H. Dai and Y. Yuan, *A nonlinear conjugate gradient method with a strong global
convergence property*, SIAM J. Optim. 10 (1999), 177-182. The Fletcher–Reeves, Polak–Ribière–
Polyak and Hestenes–Stiefel methods need the strong Wolfe conditions, and Polak–Ribière–Polyak may
fail to converge even then (Powell's examples); the Dai–Yuan method needs only the standard ones.
-/

@[expose] public section

namespace MathlibExt.Analysis.Optimization.DaiYuan

open scoped RealInnerProductSpace
open MathlibExt.Analysis.Optimization.LineSearch

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Dai–Yuan conjugate gradient parameter.** For the gradients `g` at the current point and `g'`
at the next point, and the current search direction `d`, `β = ‖g'‖² / ⟪d, g' - g⟫`
(Dai and Yuan, SIAM J. Optim. 10 (1999), formula (2.4)). -/
noncomputable def daiYuanBeta (g g' d : E) : ℝ :=
  ‖g'‖ ^ 2 / ⟪d, g' - g⟫

/-- **The Dai–Yuan identity.** If `⟪d, g' - g⟫ ≠ 0` and `d' = -g' + β • d` with the Dai–Yuan
parameter `β`, then `⟪g', d'⟫ = β ⟪g, d⟫` (Dai and Yuan, SIAM J. Optim. 10 (1999), equations
(2.5)-(2.6)). It makes the sign of the directional derivative propagate from one direction to the
next. -/
theorem inner_daiYuan_direction {g g' d : E} (h : ⟪d, g' - g⟫ ≠ 0) :
    ⟪g', -g' + daiYuanBeta g g' d • d⟫ = daiYuanBeta g g' d * ⟪g, d⟫ := by
  have hβ : daiYuanBeta g g' d * ⟪d, g' - g⟫ = ‖g'‖ ^ 2 := by
    unfold daiYuanBeta; field_simp
  rw [inner_sub_right, real_inner_comm g' d, real_inner_comm g d] at hβ
  rw [inner_add_right, inner_neg_right, real_inner_self_eq_norm_sq, real_inner_smul_right]
  linear_combination hβ

/-- **Descent of the Dai–Yuan direction.** If `d` is a descent direction at a point with gradient
`g` (`⟪g, d⟫ < 0`), the next gradient `g' ≠ 0` satisfies the Wolfe curvature condition
`⟪g', d⟫ ≥ σ ⟪g, d⟫` with `σ < 1`, then `⟪d, g' - g⟫ > 0` and the Dai–Yuan direction
`d' = -g' + β • d` is a descent direction: `⟪g', d'⟫ < 0` (the induction step in the proof of
Theorem 3.3 of Dai and Yuan, SIAM J. Optim. 10 (1999), inequality (3.10)). -/
theorem inner_daiYuan_direction_neg {g g' d : E} {σ : ℝ} (hσ : σ < 1) (hdesc : ⟪g, d⟫ < 0)
    (hcurv : σ * ⟪g, d⟫ ≤ ⟪g', d⟫) (hg' : g' ≠ 0) :
    0 < ⟪d, g' - g⟫ ∧ ⟪g', -g' + daiYuanBeta g g' d • d⟫ < 0 := by
  have hpos : 0 < ⟪d, g' - g⟫ := by
    rw [inner_sub_right, real_inner_comm g' d, real_inner_comm g d]
    nlinarith
  refine ⟨hpos, ?_⟩
  rw [inner_daiYuan_direction hpos.ne']
  have hβ : 0 < daiYuanBeta g g' d := by
    unfold daiYuanBeta
    have : 0 < ‖g'‖ := norm_pos_iff.mpr hg'
    positivity
  exact mul_neg_of_pos_of_neg hβ hdesc

/-- Algebraic core of the recurrence (3.13) of Dai and Yuan (1999). -/
private theorem ratio_step {β s D G : ℝ} (hβ : β ≠ 0) (hs : s ≠ 0) (hG : 0 < G) :
    (β ^ 2 * D - 2 * (β * s) - G) / (β * s) ^ 2 ≤ D / s ^ 2 + 1 / G := by
  have ht : β * s ≠ 0 := mul_ne_zero hβ hs
  rw [div_add_div _ _ (pow_ne_zero 2 hs) hG.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sq_nonneg s) (sq_nonneg (β * s + G))]

/-- **Global convergence of the Dai–Yuan method.** Let `x (k + 1) = x k + α k • d k` with
`α k > 0`, `d 0 = -∇f(x 0)` and `d (k + 1) = -∇f(x (k + 1)) + β k • d k` with the Dai–Yuan
parameter `β k`, where every step length satisfies the standard Wolfe conditions with constants
`δ > 0` and `σ < 1`. Suppose `f` is bounded below along the iterates,
`‖∇f(x (k + 1)) - ∇f(x k)‖ ≤ L ‖x (k + 1) - x k‖` for some `L > 0`, and no gradient vanishes (the
method does not stop at a stationary point). Then `liminf ‖∇f(x k)‖ = 0`: for every `ε > 0` and
every `N` some `k ≥ N` has `‖∇f(x k)‖ < ε`.

This is Theorem 3.3 of Y. H. Dai and Y. Yuan, SIAM J. Optim. 10 (1999), 177-182, under the
consequences of its Assumption 3.1 that its proof uses (see `LineSearch.zoutendijk`). The proof
follows the source: every direction is a descent direction; squaring `d (k + 1) + g (k + 1) =
β k • d k` and using `⟪g (k + 1), d (k + 1)⟫ = β k ⟪g k, d k⟫` gives
`‖d k‖² / ⟪g k, d k⟫² ≤ ∑_{i ≤ k} 1 / ‖g i‖²`, which contradicts the Zoutendijk condition if the
gradients stay away from zero. -/
theorem daiYuan_liminf_norm_gradient [CompleteSpace E] {f : E → ℝ} {δ σ L : ℝ} (hδ : 0 < δ)
    (hσ : σ < 1) (hL : 0 < L) {x d : ℕ → E} {α : ℕ → ℝ}
    (hx : ∀ k, x (k + 1) = x k + α k • d k) (hα : ∀ k, 0 < α k)
    (hd0 : d 0 = -gradient f (x 0))
    (hd : ∀ k, d (k + 1) =
      -gradient f (x (k + 1)) +
        daiYuanBeta (gradient f (x k)) (gradient f (x (k + 1))) (d k) • d k)
    (hwolfe : ∀ k, WolfeConditions f δ σ (x k) (d k) (α k))
    (hlip : ∀ k, ‖gradient f (x (k + 1)) - gradient f (x k)‖ ≤ L * ‖x (k + 1) - x k‖)
    (hbdd : BddBelow (Set.range fun k => f (x k)))
    (hg : ∀ k, gradient f (x k) ≠ 0) :
    ∀ ε > 0, ∀ N : ℕ, ∃ k ≥ N, ‖gradient f (x k)‖ < ε := by
  set g : ℕ → E := fun k => gradient f (x k) with hgdef
  have hcurv : ∀ k, σ * ⟪g k, d k⟫ ≤ ⟪g (k + 1), d k⟫ := by
    intro k
    have h := (hwolfe k).2
    unfold CurvatureCondition at h
    simpa [hgdef, hx k] using h
  -- Every direction is a descent direction.
  have hdesc : ∀ k, ⟪g k, d k⟫ < 0 := by
    intro k
    induction k with
    | zero =>
      rw [hd0, inner_neg_right, real_inner_self_eq_norm_sq, neg_lt_zero]
      exact pow_pos (norm_pos_iff.mpr (hg 0)) 2
    | succ k ih =>
      rw [hd k]
      exact (inner_daiYuan_direction_neg hσ ih (hcurv k) (hg (k + 1))).2
  have hden : ∀ k, 0 < ⟪d k, g (k + 1) - g k⟫ := fun k =>
    (inner_daiYuan_direction_neg hσ (hdesc k) (hcurv k) (hg (k + 1))).1
  have hβpos : ∀ k, 0 < daiYuanBeta (g k) (g (k + 1)) (d k) := by
    intro k
    unfold daiYuanBeta
    have := norm_pos_iff.mpr (hg (k + 1))
    have := hden k
    positivity
  -- The Zoutendijk condition.
  have hsum := zoutendijk hδ hσ hL hx hα hdesc hwolfe hlip hbdd
  -- The recurrence (3.13)-(3.14).
  have hratio : ∀ k, ‖d k‖ ^ 2 / ⟪g k, d k⟫ ^ 2 ≤
      ∑ i ∈ Finset.range (k + 1), 1 / ‖g i‖ ^ 2 := by
    intro k
    induction k with
    | zero =>
      have hG : 0 < ‖g 0‖ := norm_pos_iff.mpr (hg 0)
      rw [hd0, inner_neg_right, real_inner_self_eq_norm_sq, norm_neg]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      rw [neg_sq]
      apply le_of_eq
      field_simp
      rfl
    | succ k ih =>
      set β := daiYuanBeta (g k) (g (k + 1)) (d k)
      set s := ⟪g k, d k⟫
      have hts : ⟪g (k + 1), d (k + 1)⟫ = β * s := by
        rw [hd k]; exact inner_daiYuan_direction (hden k).ne'
      have hnorm : ‖d (k + 1)‖ ^ 2 = β ^ 2 * ‖d k‖ ^ 2 - 2 * (β * s) - ‖g (k + 1)‖ ^ 2 := by
        have h1 : d (k + 1) = β • d k - g (k + 1) := by rw [hd k]; abel
        have e1 : ‖d (k + 1)‖ ^ 2 =
            β ^ 2 * ‖d k‖ ^ 2 - 2 * (β * ⟪g (k + 1), d k⟫) + ‖g (k + 1)‖ ^ 2 := by
          rw [h1, norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
            real_inner_smul_left, real_inner_comm (g (k + 1)) (d k)]
        have e2 : β * s = β * ⟪g (k + 1), d k⟫ - ‖g (k + 1)‖ ^ 2 := by
          rw [← hts, h1, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
        rw [e1, e2]
        ring
      have hG : 0 < ‖g (k + 1)‖ ^ 2 := by
        have := norm_pos_iff.mpr (hg (k + 1)); positivity
      rw [hnorm, hts, Finset.sum_range_succ]
      calc (β ^ 2 * ‖d k‖ ^ 2 - 2 * (β * s) - ‖g (k + 1)‖ ^ 2) / (β * s) ^ 2
          ≤ ‖d k‖ ^ 2 / s ^ 2 + 1 / ‖g (k + 1)‖ ^ 2 :=
            ratio_step (hβpos k).ne' (hdesc k).ne hG
        _ ≤ _ := by gcongr
  -- If the gradients stayed away from zero, the Zoutendijk series would diverge.
  have hnot : ¬ ∃ c > 0, ∀ k, c ≤ ‖g k‖ := by
    rintro ⟨c, hc, hck⟩
    have hlow : ∀ k : ℕ, c ^ 2 * (1 / ((k : ℝ) + 1)) ≤ ⟪g k, d k⟫ ^ 2 / ‖d k‖ ^ 2 := by
      intro k
      have hs : 0 < ⟪g k, d k⟫ ^ 2 := by have := (hdesc k).ne; positivity
      have hdk : d k ≠ 0 := by
        intro h0; have := hdesc k; simp [h0] at this
      have hD : 0 < ‖d k‖ ^ 2 := by positivity
      have hbound : ‖d k‖ ^ 2 / ⟪g k, d k⟫ ^ 2 ≤ ((k : ℝ) + 1) / c ^ 2 := by
        refine (hratio k).trans ?_
        calc ∑ i ∈ Finset.range (k + 1), 1 / ‖g i‖ ^ 2
            ≤ ∑ _i ∈ Finset.range (k + 1), 1 / c ^ 2 :=
              Finset.sum_le_sum fun i _ => by gcongr; exact hck i
          _ = ((k : ℝ) + 1) / c ^ 2 := by simp [div_eq_mul_inv]
      rw [div_le_div_iff₀ hs (by positivity)] at hbound
      rw [mul_one_div, div_le_div_iff₀ (by positivity) hD]
      nlinarith
    have hsum' : Summable fun k : ℕ => c ^ 2 * (1 / ((k : ℝ) + 1)) :=
      Summable.of_nonneg_of_le (fun k => by positivity) hlow hsum
    have h1 : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) := by
      have := hsum'.mul_left (1 / c ^ 2)
      refine this.congr fun k => ?_
      field_simp
    have h2 : Summable fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one] using h1
    exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp h2)
  -- From "not bounded away from zero" to `liminf = 0`, using that no gradient vanishes.
  have key : ∀ N, ∀ ε > 0, (∀ k ≥ N, ε ≤ ‖g k‖) → ∃ c > 0, ∀ k, c ≤ ‖g k‖ := by
    intro N
    induction N with
    | zero => exact fun ε hε h => ⟨ε, hε, fun k => h k (Nat.zero_le k)⟩
    | succ N ih =>
      intro ε hε h
      refine ih (min ε ‖g N‖) (lt_min hε (norm_pos_iff.mpr (hg N))) fun k hk => ?_
      rcases Nat.eq_or_lt_of_le hk with rfl | hlt
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (h k hlt)
  intro ε hε N
  by_contra hcon
  push Not at hcon
  exact hnot (key N ε hε hcon)

end MathlibExt.Analysis.Optimization.DaiYuan
