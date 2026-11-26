/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.Convex.ExpConcave
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Bornology

/-!
# Tests for the quadratic lower bound for exp-concave functions

The bound specialises to `EuclideanSpace ℝ (Fin n)`. For `-log` on `[1, 2]` (`1`-exp-concave,
gradients of norm at most `1`, diameter `1`) the gradient form gives `log 2 ≤ 3 / 4`. A zero
gradient (`G = 0`) allows `γ = α / 2` and gives minimality, and `γ = 0` shows that a gradient
within `K` is a subgradient. At the kink `0` of `-log (2 - |z|)` on `[-1/2, 1/2]` there is no
derivative, but `1 / 4` is a subgradient and the bound applies. On the unbounded set `[0, ∞)`,
whose `Metric.diam` is `0`, the function `-log (1 + z)` meets every other hypothesis with `D = 0`
and `γ = 1 / 2`, but the conclusion fails: boundedness is needed.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.Convex.ExpConcave

open Real Set Filter Topology MathlibExt.Analysis.Convex.ExpConcave
open scoped InnerProductSpace

/-- The bound in `ℝⁿ`. -/
theorem quadratic_lower_bound_euclidean {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {α γ G D : ℝ} {x y g : EuclideanSpace ℝ (Fin n)}
    (hα : 0 < α) (hexp : ConcaveOn ℝ K fun z ↦ exp (-(α * f z)))
    (hK : Bornology.IsBounded K) (hD : Metric.diam K ≤ D) (hx : x ∈ K) (hy : y ∈ K)
    (hg : ∀ z ∈ K, f y + ⟪g, z - y⟫_ℝ ≤ f z) (hgG : ‖g‖ ≤ G) (hγα : 2 * γ ≤ α)
    (hγGD : 2 * γ * (G * D) ≤ 1) :
    f y + ⟪g, x - y⟫_ℝ + γ / 2 * ⟪g, x - y⟫_ℝ ^ 2 ≤ f x :=
  quadratic_lower_bound hα hexp hK hD hx hy hg hgG hγα hγGD

/-- `-log` is `1`-exp-concave on `[1, 2]`; the bound at `y = 1`, `x = 2` with `γ = 1 / 2` reads
`-1 + 1 / 4 ≤ -log 2`. -/
theorem log_two_le : log 2 ≤ 3 / 4 := by
  have hexp : ConcaveOn ℝ (Icc (1 : ℝ) 2) fun z ↦ exp (-(1 * -log z)) := by
    refine (concaveOn_id (convex_Icc (1 : ℝ) 2)).congr fun z hz ↦ ?_
    have hz0 : 0 < z := lt_of_lt_of_le one_pos hz.1
    simp [exp_log hz0]
  have hg : HasGradientWithinAt (fun z : ℝ ↦ -log z) (-1) (Icc 1 2) 1 := by
    have h := (hasDerivAt_log (one_ne_zero : (1 : ℝ) ≠ 0)).neg
    rw [inv_one] at h
    exact hasGradientWithinAt_iff_hasFDerivWithinAt.2
      (hasGradientAt_iff_hasFDerivAt.1 h.hasGradientAt').hasFDerivWithinAt
  have hD : Metric.diam (Icc (1 : ℝ) 2) ≤ 1 := by
    rw [Real.diam_Icc (by norm_num)]
    norm_num
  have h := quadratic_lower_bound_of_hasGradientWithinAt (γ := 1 / 2) (G := 1) (x := 2)
    one_pos hexp (Metric.isBounded_Icc 1 2) hD (by norm_num) (by norm_num) hg (by norm_num)
    (by norm_num) (by norm_num)
  simp only [RCLike.inner_apply, conj_trivial, log_one, neg_zero] at h
  linarith

/-- With a zero gradient the bound holds with `G = 0` and `γ = α / 2`, and `y` minimises `f`
on `K`. -/
theorem le_of_hasGradientWithinAt_zero {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {α : ℝ} {x y : EuclideanSpace ℝ (Fin n)}
    (hα : 0 < α) (hexp : ConcaveOn ℝ K fun z ↦ exp (-(α * f z)))
    (hK : Bornology.IsBounded K) (hx : x ∈ K) (hy : y ∈ K)
    (hg : HasGradientWithinAt f 0 K y) : f y ≤ f x := by
  have h := quadratic_lower_bound_of_hasGradientWithinAt (γ := α / 2) (G := 0) hα hexp hK
    le_rfl hx hy hg (by simp) (by linarith) (by simp)
  simpa using h

/-- With `γ = 0` the gradient form is the first-order convexity inequality: a gradient of an
exp-concave function within `K` is a subgradient. -/
theorem add_inner_le_of_hasGradientWithinAt {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {α : ℝ} {x y g : EuclideanSpace ℝ (Fin n)}
    (hα : 0 < α) (hexp : ConcaveOn ℝ K fun z ↦ exp (-(α * f z)))
    (hK : Bornology.IsBounded K) (hx : x ∈ K) (hy : y ∈ K)
    (hg : HasGradientWithinAt f g K y) : f y + ⟪g, x - y⟫_ℝ ≤ f x := by
  have h := quadratic_lower_bound_of_hasGradientWithinAt (γ := 0) hα hexp hK le_rfl hx hy hg
    le_rfl (by linarith) (by simp)
  simpa using h

/-- A kink: `-log (2 - |z|)` is `1`-exp-concave on `[-1/2, 1/2]` and has no derivative at `0`,
but `1 / 4` is a subgradient there, so the bound holds with `G = 1 / 4`, `D = 1` and
`γ = 1 / 2`. -/
theorem kink :
    ¬ DifferentiableAt ℝ (fun z : ℝ ↦ -log (2 - |z|)) 0 ∧
      ∀ x ∈ Icc (-(1 / 2) : ℝ) (1 / 2), -log (2 - |(0 : ℝ)|) + ⟪(1 / 4 : ℝ), x - 0⟫_ℝ +
        1 / 2 / 2 * ⟪(1 / 4 : ℝ), x - 0⟫_ℝ ^ 2 ≤ -log (2 - |x|) := by
  have hpos : ∀ z ∈ Icc (-(1 / 2) : ℝ) (1 / 2), 0 < 2 - |z| := fun z hz ↦ by
    have := abs_le.2 ⟨hz.1, hz.2⟩
    linarith
  have hexp : ConcaveOn ℝ (Icc (-(1 / 2) : ℝ) (1 / 2)) fun z ↦ exp (-(1 * -log (2 - |z|))) := by
    have hc : ConcaveOn ℝ (Icc (-(1 / 2) : ℝ) (1 / 2)) (fun z : ℝ ↦ -‖z‖ + 2) :=
      (convexOn_norm (convex_Icc _ _)).neg.add_const 2
    refine hc.congr fun z hz ↦ ?_
    simp only [one_mul, neg_neg, exp_log (hpos z hz), Real.norm_eq_abs]
    ring
  have hsub : ∀ z ∈ Icc (-(1 / 2) : ℝ) (1 / 2),
      -log (2 - |(0 : ℝ)|) + ⟪(1 / 4 : ℝ), z - 0⟫_ℝ ≤ -log (2 - |z|) := by
    intro z hz
    simp only [abs_zero, sub_zero, RCLike.inner_apply, conj_trivial]
    have h2 := hpos z hz
    have hlog : log ((2 - |z|) / 2) ≤ (2 - |z|) / 2 - 1 := log_le_sub_one_of_pos (by positivity)
    rw [log_div h2.ne' (by norm_num)] at hlog
    have : z * (1 / 4) ≤ |z| / 2 := by
      rcases le_total 0 z with h | h
      · rw [abs_of_nonneg h]; linarith
      · rw [abs_of_nonpos h]; linarith
    nlinarith
  have h0 : (0 : ℝ) ∈ Icc (-(1 / 2) : ℝ) (1 / 2) := by norm_num
  have hD : Metric.diam (Icc (-(1 / 2) : ℝ) (1 / 2)) ≤ 1 := by
    rw [Real.diam_Icc (by norm_num)]
    norm_num
  refine ⟨fun hd ↦ not_differentiableAt_abs_zero ?_, fun x hx ↦
    quadratic_lower_bound (γ := 1 / 2) (G := 1 / 4) one_pos hexp (Metric.isBounded_Icc _ _) hD hx
      h0 hsub (by norm_num) (by norm_num) (by norm_num)⟩
  have hφ : DifferentiableAt ℝ (fun z : ℝ ↦ 2 - exp (-(-log (2 - |z|)))) 0 :=
    (differentiableAt_const 2).sub hd.neg.exp
  refine hφ.congr_of_eventuallyEq ?_
  have hnhds : {z : ℝ | |z| < 2} ∈ 𝓝 (0 : ℝ) :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by norm_num)
  filter_upwards [hnhds] with z hz
  have h2 : 0 < 2 - |z| := by linarith [show |z| < 2 from hz]
  simp only [neg_neg, exp_log h2]
  ring

/-- Boundedness cannot be dropped: `Metric.diam [0, ∞) = 0`, and `-log (1 + z)` is
`1`-exp-concave on `[0, ∞)` with subgradient `-1` at `0`, so every other hypothesis holds with
`D = 0`, `G = 1` and `γ = 1 / 2`; yet at `y = 0`, `x = 8` the left side is `8` and the right side
`-log 9` is negative. -/
theorem isBounded_needed :
    ¬ Bornology.IsBounded (Ici (0 : ℝ)) ∧ Metric.diam (Ici (0 : ℝ)) = 0 ∧
      (ConcaveOn ℝ (Ici 0) fun z : ℝ ↦ exp (-(1 * -log (1 + z)))) ∧
      (∀ z ∈ Ici (0 : ℝ), -log (1 + 0) + ⟪(-1 : ℝ), z - 0⟫_ℝ ≤ -log (1 + z)) ∧
      ¬ (-log (1 + 0) + ⟪(-1 : ℝ), 8 - 0⟫_ℝ + 1 / 2 / 2 * ⟪(-1 : ℝ), 8 - 0⟫_ℝ ^ 2 ≤
        -log (1 + 8)) := by
  have hunb : ¬ Bornology.IsBounded (Ici (0 : ℝ)) := fun h ↦ not_bddAbove_Ici 0 h.bddAbove
  refine ⟨hunb, Metric.diam_eq_zero_of_unbounded hunb, ?_, ?_, ?_⟩
  · refine ((concaveOn_id (convex_Ici (0 : ℝ))).add_const 1).congr fun z hz ↦ ?_
    have hz0 : 0 < 1 + z := by linarith [mem_Ici.1 hz]
    simp only [one_mul, neg_neg]
    rw [exp_log hz0, Pi.add_apply, id, add_comm]
  · intro z hz
    have hz0 : 0 < 1 + z := by linarith [mem_Ici.1 hz]
    have := log_le_sub_one_of_pos hz0
    simp only [RCLike.inner_apply, conj_trivial, add_zero, log_one, neg_zero, sub_zero]
    linarith
  · simp only [RCLike.inner_apply, conj_trivial, add_zero, log_one, neg_zero]
    have : 0 < log (1 + 8 : ℝ) := log_pos (by norm_num)
    intro h
    norm_num at h this
    linarith

end MathlibExtTest.Analysis.Convex.ExpConcave
