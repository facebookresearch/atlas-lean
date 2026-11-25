/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Variational.MinimizingMovement
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Contraction of minimizing movements for `λ`-convex functionals

F. Otto's picture of dissipative equations as gradient flows explains contraction estimates by
convexity: "the contraction property … follows from the convexity of `E`" (F. Otto and
M. Westdickenberg, *Eulerian calculus for the contraction in the Wasserstein distance*,
Section 1, for the porous medium equation, where the convexity is McCann's displacement
convexity). In a Hilbert space the time-discrete version of this principle is elementary: if `F`
is `λ`-convex, one step of the minimizing-movement scheme with time step `h` is a
`(1 + λh)⁻¹`-Lipschitz map, the implicit-Euler counterpart of the contraction factor `e^{-λt}`.

This file proves it on a real inner product space. `λ`-convexity is Mathlib's
`StrongConvexOn univ λ F`, i.e. `F((1-t)a + tb) ≤ (1-t)F(a) + tF(b) - t(1-t)(λ/2)|a - b|²`;
`λ` may be negative as long as `1 + λh > 0`.

## Main results

* `IsMinimizingMovementStep.inner_le`: the variational inequality characterizing the step.
* `IsMinimizingMovementStep.contraction`: `(1 + λh) ‖y₁ - y₂‖ ≤ ‖x₁ - x₂‖`.
* `IsMinimizingMovement.contraction_pow`: `(1 + λh)ᵏ ‖ρ¹ₖ - ρ²ₖ‖ ≤ ‖ρ¹₀ - ρ²₀‖`.
-/

@[expose] public section

open Set
open scoped RealInnerProductSpace

namespace MathlibExt.Analysis.Variational.MinimizingMovement

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- If `a ≤ b + t c` for every `t ∈ (0, 1]`, then `a ≤ b`.
private theorem le_of_forall_Ioc_le_add_mul {a b c : ℝ}
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → a ≤ b + t * c) : a ≤ b := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  set t : ℝ := min 1 (ε / (|c| + 1)) with ht
  have hc1 : 0 < |c| + 1 := by positivity
  have ht0 : 0 < t := lt_min one_pos (div_pos hε hc1)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htε : t ≤ ε / (|c| + 1) := min_le_right _ _
  have key := h t ht0 ht1
  have : t * c ≤ t * |c| := mul_le_mul_of_nonneg_left (le_abs_self c) ht0.le
  have : t * |c| < ε := by
    calc t * |c| ≤ ε / (|c| + 1) * |c| := mul_le_mul_of_nonneg_right htε (abs_nonneg c)
      _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hc1]
        nlinarith [abs_nonneg c]
  linarith

/-- **Variational inequality of the minimizing-movement step.** On a real inner product space,
if `F` is `λ`-convex and `y` is a minimizing-movement step from `x` with time step `h > 0`, then
for every `z`,
`⟪x - y, z - y⟫ ≤ h (F(z) - F(y)) - h (λ/2) ‖z - y‖²`,
i.e. `(x - y)/h` is a `λ`-subgradient of `F` at `y` (the implicit Euler equation
`y = x - h ∇F(y)` when `F` is differentiable). -/
theorem IsMinimizingMovementStep.inner_le {F : H → ℝ} {lam h : ℝ}
    (hF : StrongConvexOn univ lam F) (hh : 0 < h) {x y : H}
    (hy : IsMinimizingMovementStep F h x y) (z : H) :
    ⟪x - y, z - y⟫ ≤ h * (F z - F y) - h * (lam / 2) * ‖z - y‖ ^ 2 := by
  apply le_of_forall_Ioc_le_add_mul (c := ‖z - y‖ ^ 2 / 2 + h * (lam / 2) * ‖z - y‖ ^ 2)
  intro t ht0 ht1
  set w : H := (1 - t) • y + t • z with hw
  have hstep := hy w
  have hconv := hF.2 (mem_univ y) (mem_univ z) (by linarith : 0 ≤ 1 - t) ht0.le
    (by ring : (1 - t) + t = 1)
  simp only [smul_eq_mul] at hconv
  have hxw : x - w = (x - y) - t • (z - y) := by
    rw [hw]; module
  have hnorm : ‖x - w‖ ^ 2 = ‖x - y‖ ^ 2 - 2 * t * ⟪x - y, z - y⟫ + t ^ 2 * ‖z - y‖ ^ 2 := by
    rw [hxw, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs]
    ring
  rw [dist_eq_norm, dist_eq_norm, hnorm] at hstep
  have hyz : ‖y - z‖ = ‖z - y‖ := norm_sub_rev y z
  rw [hyz] at hconv
  -- `hstep` and `hconv` combine to `t ⟪x - y, z - y⟫ ≤ t (RHS)`
  have hmain : t * ⟪x - y, z - y⟫ ≤ t * (h * (F z - F y) - h * (lam / 2) * ‖z - y‖ ^ 2 +
      t * (‖z - y‖ ^ 2 / 2 + h * (lam / 2) * ‖z - y‖ ^ 2)) := by
    have := mul_le_mul_of_nonneg_left hconv hh.le
    nlinarith
  exact le_of_mul_le_mul_left hmain ht0

/-- **Contraction of the minimizing-movement step.** On a real inner product space, let `F` be
`λ`-convex, `h > 0`, and let `y₁`, `y₂` be minimizing-movement steps from `x₁`, `x₂`. Then
`(1 + λh) ‖y₁ - y₂‖ ≤ ‖x₁ - x₂‖`: when `1 + λh > 0` the step is `(1 + λh)⁻¹`-Lipschitz, and in
particular unique. This is the time-discrete form of the principle that gradient flows of
convex functionals contract (F. Otto and M. Westdickenberg, *Eulerian calculus for the
contraction in the Wasserstein distance*, Section 1); the proof adds the variational
inequalities of the two steps. -/
theorem IsMinimizingMovementStep.contraction {F : H → ℝ} {lam h : ℝ}
    (hF : StrongConvexOn univ lam F) (hh : 0 < h) {x₁ x₂ y₁ y₂ : H}
    (hy₁ : IsMinimizingMovementStep F h x₁ y₁) (hy₂ : IsMinimizingMovementStep F h x₂ y₂) :
    (1 + lam * h) * ‖y₁ - y₂‖ ≤ ‖x₁ - x₂‖ := by
  have h1 := hy₁.inner_le hF hh y₂
  have h2 := hy₂.inner_le hF hh y₁
  have hsym : ‖y₁ - y₂‖ = ‖y₂ - y₁‖ := norm_sub_rev _ _
  -- sum of the two variational inequalities
  have hsum : ⟪x₁ - y₁, y₂ - y₁⟫ + ⟪x₂ - y₂, y₁ - y₂⟫ ≤ -(h * lam) * ‖y₁ - y₂‖ ^ 2 := by
    rw [← hsym] at h1
    nlinarith
  have hexp : ⟪x₁ - y₁, y₂ - y₁⟫ + ⟪x₂ - y₂, y₁ - y₂⟫ =
      ‖y₁ - y₂‖ ^ 2 - ⟪x₁ - x₂, y₁ - y₂⟫ := by
    have e1 : y₂ - y₁ = -(y₁ - y₂) := by abel
    rw [e1, inner_neg_right, ← real_inner_self_eq_norm_sq]
    have e2 : x₁ - y₁ = (x₁ - x₂) + (x₂ - y₂) - (y₁ - y₂) := by abel
    rw [e2, inner_sub_left, inner_add_left]
    ring
  have hcs : ⟪x₁ - x₂, y₁ - y₂⟫ ≤ ‖x₁ - x₂‖ * ‖y₁ - y₂‖ := real_inner_le_norm _ _
  have hq : (1 + lam * h) * ‖y₁ - y₂‖ ^ 2 ≤ ‖x₁ - x₂‖ * ‖y₁ - y₂‖ := by nlinarith
  rcases (norm_nonneg (y₁ - y₂)).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; exact norm_nonneg _
  · have : (1 + lam * h) * ‖y₁ - y₂‖ * ‖y₁ - y₂‖ ≤ ‖x₁ - x₂‖ * ‖y₁ - y₂‖ := by nlinarith
    exact le_of_mul_le_mul_right this hpos

/-- **Discrete exponential contraction of minimizing movements.** On a real inner product space,
for a `λ`-convex `F`, a time step `h > 0` with `1 + λh > 0`, and two minimizing-movement
sequences `ρ¹`, `ρ²`, `(1 + λh)ᵏ ‖ρ¹ₖ - ρ²ₖ‖ ≤ ‖ρ¹₀ - ρ²₀‖` for every `k`: the implicit-Euler
counterpart of `‖ρ¹(t) - ρ²(t)‖ ≤ e^{-λt} ‖ρ¹(0) - ρ²(0)‖`. -/
theorem IsMinimizingMovement.contraction_pow {F : H → ℝ} {lam h : ℝ}
    (hF : StrongConvexOn univ lam F) (hh : 0 < h) (hlh : 0 < 1 + lam * h) {ρ₁ ρ₂ : ℕ → H}
    (hρ₁ : IsMinimizingMovement F h ρ₁) (hρ₂ : IsMinimizingMovement F h ρ₂) (k : ℕ) :
    (1 + lam * h) ^ k * ‖ρ₁ k - ρ₂ k‖ ≤ ‖ρ₁ 0 - ρ₂ 0‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep := (hρ₁ k).contraction hF hh (hρ₂ k)
    have hpow : 0 ≤ (1 + lam * h) ^ k := pow_nonneg hlh.le k
    calc (1 + lam * h) ^ (k + 1) * ‖ρ₁ (k + 1) - ρ₂ (k + 1)‖
        = (1 + lam * h) ^ k * ((1 + lam * h) * ‖ρ₁ (k + 1) - ρ₂ (k + 1)‖) := by ring
      _ ≤ (1 + lam * h) ^ k * ‖ρ₁ k - ρ₂ k‖ := mul_le_mul_of_nonneg_left hstep hpow
      _ ≤ ‖ρ₁ 0 - ρ₂ 0‖ := ih

end MathlibExt.Analysis.Variational.MinimizingMovement
