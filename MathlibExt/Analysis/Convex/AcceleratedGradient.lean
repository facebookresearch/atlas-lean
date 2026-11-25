/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
import MathlibExt.Analysis.Convex.GradientDescent
import MathlibExt.Analysis.Convex.FirstOrderCondition

/-!
# Nesterov's accelerated gradient method

Nesterov's accelerated gradient method for a convex function `f` with `L`-Lipschitz gradient on a
real Hilbert space, in the three-sequence (linear-coupling) form

* `x (k + 1) = (A k / A (k + 1)) • y k + (a k / A (k + 1)) • z k`, the coupling step;
* `y (k + 1) = x (k + 1) - (1 / L) • ∇f (x (k + 1))`, a gradient step;
* `z (k + 1) = z k - a k • ∇f (x (k + 1))`, a dual-averaging (mirror-descent) step with weight
  `a k = A (k + 1) - A k`.

This is the family (19a)-(19c) of A. C. Wilson, B. Recht and M. I. Jordan, *A Lyapunov analysis
of momentum methods in optimization* (arXiv:1611.02635v4), with Euclidean distance-generating
function `h = ‖·‖² / 2` and the map `G` a gradient step at `x (k + 1)`. Their discrete Lyapunov
function (21), `E k = ‖z k - u‖² / 2 + A k * (f (y k) - f u)`, does not increase as soon as
`L * a k ^ 2 ≤ A (k + 1)`; with `A k = k (k + 1) / (4 L)` this gives Nesterov's `O(1 / k²)` rate.

## Main results

* `accelerated_lyapunov_step`: one step does not increase the Lyapunov function.
* `accelerated_lyapunov_le`: the Lyapunov function is bounded by its initial value.
* `nesterov_accelerated_rate`: the rate `f (y k) - f u ≤ 2 L ‖z 0 - u‖² / (k (k + 1))`.
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.AcceleratedGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

private theorem first_order {f : E → ℝ} (hconvex : ConvexOn ℝ Set.univ f)
    (hdiff : Differentiable ℝ f) (x y : E) : f x + inner ℝ (gradient f x) (y - x) ≤ f y := by
  have h := MathlibExt.Analysis.Convex.FirstOrderCondition.add_fderiv_le_of_convexOn hconvex
    (Set.mem_univ x) (Set.mem_univ y) (hdiff x).hasGradientAt.hasFDerivAt
  simpa [InnerProductSpace.toDual_apply_apply] using h

/-- **One step of the accelerated gradient method does not increase its Lyapunov function.**
Let `f` be convex and differentiable on a real Hilbert space with `L`-Lipschitz gradient,
`L > 0`, and let `u` be any point. Let `0 ≤ A ≤ A'` with `L * (A' - A) ^ 2 ≤ A'`, and let
`x' , y', z'` be obtained from `y, z` by the coupling `A' • x' = A • y + (A' - A) • z`, the gradient
step `y' = x' - (1 / L) • ∇f x'` and the step `z' = z - (A' - A) • ∇f x'`. Then
`A' * (f y' - f u) + ‖z' - u‖ ^ 2 / 2 ≤ A * (f y - f u) + ‖z - u‖ ^ 2 / 2`.

Source: A. C. Wilson, B. Recht and M. I. Jordan, *A Lyapunov analysis of momentum methods in
optimization*, arXiv:1611.02635v4, Section 3.1: the accelerated family (19a)-(19c), the
Lyapunov function (21), and Proposition 5 with Lemma 6 (the map `G_ε` of (25) and the error
bound (26a), which is `≤ 0` exactly when `(A' - A) ^ 2 ≤ A' / L`), here with `h = ‖·‖² / 2`,
`σ = 1` and `ε = 1 / L`. -/
theorem accelerated_lyapunov_step {f : E → ℝ} {L : ℝ} (hL : 0 < L)
    (hconvex : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (hsmooth : LipschitzWith ⟨L, le_of_lt hL⟩ (gradient f)) (u : E)
    {A A' : ℝ} (hA : 0 ≤ A) (hAA' : A ≤ A') (hstep : L * (A' - A) ^ 2 ≤ A')
    {x' y y' z z' : E} (hx : A' • x' = A • y + (A' - A) • z)
    (hy : y' = x' - (1 / L) • gradient f x') (hz : z' = z - (A' - A) • gradient f x') :
    A' * (f y' - f u) + ‖z' - u‖ ^ 2 / 2 ≤ A * (f y - f u) + ‖z - u‖ ^ 2 / 2 := by
  set g := gradient f x' with hg
  set a := A' - A with ha
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hA'0 : 0 ≤ A' := hA.trans hAA'
  have hηL : (1 / L) ∈ Set.Ioc 0 (1 / L) := ⟨by positivity, le_rfl⟩
  have hdec : f y' ≤ f x' - (1 / L) / 2 * ‖g‖ ^ 2 := by
    rw [hy]; exact MetaMathlibExt.gradientDescent_sufficient_decrease hL hdiff hsmooth hηL x'
  have hc1 := first_order hconvex hdiff x' y
  have hc2 := first_order hconvex hdiff x' u
  have hnorm : ‖z' - u‖ ^ 2 = ‖z - u‖ ^ 2 - 2 * a * inner ℝ g (z - u) + a ^ 2 * ‖g‖ ^ 2 := by
    rw [hz, show z - a • g - u = (z - u) - a • g by abel, norm_sub_sq_real, inner_smul_right,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg ha0, real_inner_comm]
    ring
  have hcouple : A' * inner ℝ g x' = A * inner ℝ g y + a * inner ℝ g z := by
    have := congrArg (inner ℝ g) hx
    simpa [inner_add_right, inner_smul_right] using this
  have hA' : A' = A + a := by rw [ha]; ring
  simp only [inner_sub_right] at hc1 hc2 hnorm
  have hg2 : 0 ≤ ‖g‖ ^ 2 := sq_nonneg _
  have hfin : a ^ 2 ≤ A' / L := by rw [le_div_iff₀ hL]; nlinarith
  have hkey : (a ^ 2 - A' / L) * ‖g‖ ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hg2
  have e1 := mul_le_mul_of_nonneg_left hc1 hA
  have e2 := mul_le_mul_of_nonneg_left hc2 ha0
  have e3 := mul_le_mul_of_nonneg_left hdec hA'0
  have hdivL : A' * ((1 / L) / 2 * ‖g‖ ^ 2) = (A' / L) * ‖g‖ ^ 2 / 2 := by
    field_simp
  rw [hnorm]
  nlinarith [e1, e2, e3, hdivL, hcouple, hkey, hA']

/-- **The Lyapunov function of the accelerated gradient method is bounded by its initial value.**
Let `f` be convex and differentiable on a real Hilbert space with `L`-Lipschitz gradient,
`L > 0`, and `u` any point. Let `A : ℕ → ℝ` be nondecreasing with `0 ≤ A 0` and
`L * (A (k + 1) - A k) ^ 2 ≤ A (k + 1)`, and let `x y z : ℕ → E` satisfy, for every `k`,
`A (k + 1) • x (k + 1) = A k • y k + (A (k + 1) - A k) • z k`,
`y (k + 1) = x (k + 1) - (1 / L) • ∇f (x (k + 1))` and
`z (k + 1) = z k - (A (k + 1) - A k) • ∇f (x (k + 1))`. Then for every `k`,
`A k * (f (y k) - f u) + ‖z k - u‖ ^ 2 / 2 ≤ A 0 * (f (y 0) - f u) + ‖z 0 - u‖ ^ 2 / 2`.

Source: A. C. Wilson, B. Recht and M. I. Jordan, *A Lyapunov analysis of momentum methods in
optimization*, arXiv:1611.02635v4, Section 3.1, the Lyapunov function (21) for the family
(19a)-(19c), with the one-step bound of Proposition 5 and Lemma 6, (25)-(26a) (Euclidean case,
`G` a gradient step). -/
theorem accelerated_lyapunov_le {f : E → ℝ} {L : ℝ} (hL : 0 < L)
    (hconvex : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (hsmooth : LipschitzWith ⟨L, le_of_lt hL⟩ (gradient f)) (u : E)
    {A : ℕ → ℝ} (hA0 : 0 ≤ A 0) (hAmono : ∀ k, A k ≤ A (k + 1))
    (hAstep : ∀ k, L * (A (k + 1) - A k) ^ 2 ≤ A (k + 1))
    {x y z : ℕ → E} (hx : ∀ k, A (k + 1) • x (k + 1) = A k • y k + (A (k + 1) - A k) • z k)
    (hy : ∀ k, y (k + 1) = x (k + 1) - (1 / L) • gradient f (x (k + 1)))
    (hz : ∀ k, z (k + 1) = z k - (A (k + 1) - A k) • gradient f (x (k + 1))) (k : ℕ) :
    A k * (f (y k) - f u) + ‖z k - u‖ ^ 2 / 2 ≤ A 0 * (f (y 0) - f u) + ‖z 0 - u‖ ^ 2 / 2 := by
  have hApos : ∀ k, 0 ≤ A k := by
    intro k
    induction k with
    | zero => exact hA0
    | succ n ih => exact ih.trans (hAmono n)
  induction k with
  | zero => exact le_rfl
  | succ n ih =>
    exact (accelerated_lyapunov_step hL hconvex hdiff hsmooth u (hApos n) (hAmono n) (hAstep n)
      (hx n) (hy n) (hz n)).trans ih

/-- **Nesterov's `O(1 / k²)` rate for accelerated gradient descent.** Let `f` be convex and
differentiable on a real Hilbert space with `L`-Lipschitz gradient, `L > 0`. Run the accelerated
gradient method from `z 0` (the point `y 0` is never used):
`x (k + 1) = (k / (k + 2)) • y k + (2 / (k + 2)) • z k`,
`y (k + 1) = x (k + 1) - (1 / L) • ∇f (x (k + 1))`,
`z (k + 1) = z k - ((k + 1) / (2 L)) • ∇f (x (k + 1))`.
Then for every point `u` and every `k ≥ 1`,
`f (y k) - f u ≤ 2 L ‖z 0 - u‖ ^ 2 / (k (k + 1))`; with `u` a minimizer this is the accelerated
rate, against `O(1 / k)` for plain gradient descent.

Source: Y. Nesterov, *A method of solving a convex programming problem with convergence rate
O(1/k²)*, Soviet Math. Dokl. 27 (1983) 372-376 (the rate); the proof is the Lyapunov argument of
A. C. Wilson, B. Recht and M. I. Jordan, arXiv:1611.02635v4, Section 3.1, function (21) for the
family (19a)-(19c) and Proposition 5 with Lemma 6, (25)-(26a), here with
`A k = k (k + 1) / (4 L)`, `τ k = 2 / (k + 2)`. -/
theorem nesterov_accelerated_rate {f : E → ℝ} {L : ℝ} (hL : 0 < L)
    (hconvex : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (hsmooth : LipschitzWith ⟨L, le_of_lt hL⟩ (gradient f)) (u : E)
    {x y z : ℕ → E}
    (hx : ∀ k : ℕ, x (k + 1) = ((k : ℝ) / (k + 2)) • y k + (2 / ((k : ℝ) + 2)) • z k)
    (hy : ∀ k, y (k + 1) = x (k + 1) - (1 / L) • gradient f (x (k + 1)))
    (hz : ∀ k : ℕ, z (k + 1) = z k - (((k : ℝ) + 1) / (2 * L)) • gradient f (x (k + 1)))
    {k : ℕ} (hk : 0 < k) :
    f (y k) - f u ≤ 2 * L * ‖z 0 - u‖ ^ 2 / ((k : ℝ) * (k + 1)) := by
  set A : ℕ → ℝ := fun k => (k : ℝ) * (k + 1) / (4 * L) with hAdef
  have hdiffA : ∀ k : ℕ, A (k + 1) - A k = ((k : ℝ) + 1) / (2 * L) := by
    intro k; simp only [hAdef]; push_cast; field_simp; ring
  have hA0 : 0 ≤ A 0 := by simp [hAdef]
  have hAmono : ∀ k, A k ≤ A (k + 1) := by
    intro k
    have := hdiffA k
    have : 0 ≤ ((k : ℝ) + 1) / (2 * L) := by positivity
    linarith
  have hAstep : ∀ k, L * (A (k + 1) - A k) ^ 2 ≤ A (k + 1) := by
    intro k
    rw [hdiffA k]
    simp only [hAdef]; push_cast
    rw [div_pow, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    have hk0 : (0 : ℝ) ≤ k := by positivity
    nlinarith [hL, hk0]
  have hx' : ∀ k, A (k + 1) • x (k + 1) = A k • y k + (A (k + 1) - A k) • z k := by
    intro k
    rw [hx k, hdiffA k, smul_add, smul_smul, smul_smul]
    congr 2
    · simp only [hAdef]; push_cast; field_simp; ring
    · simp only [hAdef]; push_cast; field_simp; ring
  have hz' : ∀ k, z (k + 1) = z k - (A (k + 1) - A k) • gradient f (x (k + 1)) := by
    intro k; rw [hdiffA k]; exact hz k
  have hlyap := accelerated_lyapunov_le hL hconvex hdiff hsmooth u hA0 hAmono hAstep hx' hy hz' k
  have hA00 : A 0 = 0 := by simp [hAdef]
  rw [hA00, zero_mul, zero_add] at hlyap
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hAk : A k = (k : ℝ) * (k + 1) / (4 * L) := rfl
  have hApos : 0 < A k := by rw [hAk]; positivity
  have hmain : A k * (f (y k) - f u) ≤ ‖z 0 - u‖ ^ 2 / 2 := by
    nlinarith [sq_nonneg ‖z k - u‖]
  rw [le_div_iff₀ (by positivity)]
  rw [hAk] at hmain
  have h4L : 0 < 4 * L := by positivity
  have := mul_le_mul_of_nonneg_left hmain h4L.le
  have hre : 4 * L * ((k : ℝ) * (k + 1) / (4 * L) * (f (y k) - f u)) =
      (f (y k) - f u) * ((k : ℝ) * (k + 1)) := by field_simp
  nlinarith [this, hre]

end MathlibExt.Analysis.Convex.AcceleratedGradient
