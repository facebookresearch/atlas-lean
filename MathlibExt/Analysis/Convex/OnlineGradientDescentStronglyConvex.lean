/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.Analysis.Convex.OnlineGradientDescent

import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Strongly convex online gradient descent regret

For `α`-strongly convex losses, online gradient descent with step sizes
`η t = 1 / (α * (t + 1))` has regret at most `(G ^ 2 / (2 * α)) * (1 + log T)`.
This is the `t = 0`-indexed form of Hazan, "Introduction to online convex
optimization", Section 3.3, Theorem 3.3.

The main result is `ogd_regret_strongly_convex`, proved from the one-step
inequality `ogd_strongly_convex_step` (telescoping distance terms) and the
harmonic-number estimate `harmonic_sum_le_one_add_log`.

This file is the time-varying strongly convex companion to the fixed-step
`ogdIter` and `ogd_regret` API in `MathlibExt.Analysis.Convex.OnlineGradientDescent`.
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.OnlineGradientDescentStronglyConvex

open scoped InnerProductSpace

/-- One-step regret inequality for strongly convex online gradient descent.

At a single round `t` with step size `η > 0`, the instantaneous regret is
bounded by a telescoping distance term, a negative strong-convexity term and a
gradient-norm term. The proof combines projection nonexpansiveness, the
squared-norm expansion of the gradient step, and strong convexity.
-/
theorem ogd_strongly_convex_step {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (proj : E → E) (f : ℕ → E → ℝ) (g : ℕ → E → E) (α η : ℝ)
    (x : ℕ → E) (xstar : E) (t : ℕ)
    (hη : 0 < η)
    (hproj : LipschitzWith 1 proj)
    (hprojstar : proj xstar = xstar)
    (hupd : x (t + 1) = proj (x t - η • g t (x t)))
    (hsc : f t (x t) + ⟪g t (x t), xstar - x t⟫_ℝ
      + (α / 2) * ‖xstar - x t‖ ^ 2 ≤ f t xstar) :
    f t (x t) - f t xstar ≤ (‖x t - xstar‖ ^ 2 - ‖x (t + 1) - xstar‖ ^ 2)
      / (2 * η) - (α / 2) * ‖xstar - x t‖ ^ 2
      + (η / 2) * ‖g t (x t)‖ ^ 2 := by
  set g0 := g t (x t) with hg0
  -- Projection nonexpansiveness at the pre-projection point.
  have hnonexp : ‖x (t + 1) - xstar‖ ≤ ‖(x t - η • g0) - xstar‖ := by
    have h := hproj.dist_le_mul (x t - η • g0) xstar
    rw [hprojstar] at h
    rw [hupd]
    simp only [dist_eq_norm, NNReal.coe_one, one_mul] at h ⊢
    exact h
  have hsq : ‖x (t + 1) - xstar‖ ^ 2 ≤ ‖(x t - η • g0) - xstar‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnonexp 2
  -- Squared-norm expansion of the unprojected gradient step.
  have hexpand : ‖(x t - η • g0) - xstar‖ ^ 2 = ‖x t - xstar‖ ^ 2
      - 2 * (η * ⟪g0, x t - xstar⟫_ℝ) + η ^ 2 * ‖g0‖ ^ 2 := by
    have h1 : (x t - η • g0) - xstar = (x t - xstar) - η • g0 := by abel
    rw [h1, norm_sub_sq_real, inner_smul_right, real_inner_comm g0 (x t - xstar),
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  -- Strong convexity, rearranged to isolate the instantaneous regret.
  have hneg : ⟪g0, xstar - x t⟫_ℝ = -⟪g0, x t - xstar⟫_ℝ := by
    rw [← neg_sub, inner_neg_right]
  have hB : f t (x t) - f t xstar
      ≤ ⟪g0, x t - xstar⟫_ℝ - (α / 2) * ‖xstar - x t‖ ^ 2 := by
    have h := hsc
    rw [hneg] at h
    linarith
  -- Distance bookkeeping bounds the alignment term.
  have hA : 2 * η * ⟪g0, x t - xstar⟫_ℝ
      ≤ (‖x t - xstar‖ ^ 2 - ‖x (t + 1) - xstar‖ ^ 2)
        + η ^ 2 * ‖g0‖ ^ 2 := by
    have h := hsq
    rw [hexpand] at h
    linarith
  -- Divide by `2 * η` and combine.
  have h2η : (0 : ℝ) < 2 * η := by linarith
  have hdiv : ⟪g0, x t - xstar⟫_ℝ - (η / 2) * ‖g0‖ ^ 2
      ≤ (‖x t - xstar‖ ^ 2 - ‖x (t + 1) - xstar‖ ^ 2) / (2 * η) := by
    rw [le_div_iff₀ h2η]
    have hring : (⟪g0, x t - xstar⟫_ℝ - (η / 2) * ‖g0‖ ^ 2) * (2 * η)
        = 2 * η * ⟪g0, x t - xstar⟫_ℝ - η ^ 2 * ‖g0‖ ^ 2 := by ring
    rw [hring]
    linarith [hA]
  have hI : ⟪g0, x t - xstar⟫_ℝ
      ≤ (‖x t - xstar‖ ^ 2 - ‖x (t + 1) - xstar‖ ^ 2) / (2 * η)
        + (η / 2) * ‖g0‖ ^ 2 :=
    sub_le_iff_le_add.mp hdiv
  linarith [hB, hI]

/-- Harmonic partial sums grow at most logarithmically:
`∑ t ∈ range T, 1 / (t + 1) ≤ 1 + log T` for `1 ≤ T`. -/
theorem harmonic_sum_le_one_add_log (T : ℕ) (_hT : 1 ≤ T) :
    ∑ t ∈ Finset.range T, (1 : ℝ) / ((t : ℝ) + 1) ≤ 1 + Real.log T := by
  have h := harmonic_le_one_add_log T
  unfold harmonic at h
  rw [Rat.cast_sum] at h
  simp only [Rat.cast_inv, Nat.cast_add, Nat.cast_one, Rat.cast_add, Rat.cast_one,
    Rat.cast_natCast] at h
  simp only [← inv_eq_one_div]
  exact h

/-- Regret of online gradient descent for `α`-strongly convex losses.

With step sizes `η t = 1 / (α * (t + 1))` and subgradients bounded by `G`,
the regret against any comparator fixed by the projection is at most
`(G ^ 2 / (2 * α)) * (1 + log T)`.

Indexing starts at `t = 0`, so the classical schedule `η t = 1 / (α * t)`
for `t = 1, .., T` appears here as `η t = 1 / (α * (t + 1))` for
`t = 0, .., T - 1`. The iterate sequence is not constructed here: any
sequence satisfying the projected-gradient update hypothesis `hupd` (whose
existence is elementary by recursion) enjoys the bound.

Only the comparator instance of strong convexity is assumed: no
strong-convexity inequality outside the comparator instance is assumed.
Feasible-set strong convexity supplies this hypothesis for feasible iterates
and comparator.

As `α → 0` both the step-size schedule and the regret bound blow up; there
is no claim at `α = 0` (the bound is infinite and the schedule undefined).
-/
theorem ogd_regret_strongly_convex {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (proj : E → E) (f : ℕ → E → ℝ) (g : ℕ → E → E) (α G : ℝ)
    (x : ℕ → E) (xstar : E) (T : ℕ)
    (hα : 0 < α) (_hG0 : 0 ≤ G)
    (hproj : LipschitzWith 1 proj)
    (hprojstar : proj xstar = xstar)
    (hupd : ∀ t, x (t + 1)
      = proj (x t - (1 / (α * ((t : ℝ) + 1))) • g t (x t)))
    (hsc : ∀ t : ℕ, f t (x t) + ⟪g t (x t), xstar - x t⟫_ℝ
      + (α / 2) * ‖xstar - x t‖ ^ 2 ≤ f t xstar)
    (hG : ∀ t, ‖g t (x t)‖ ≤ G)
    (hT : 1 ≤ T) :
    ∑ t ∈ Finset.range T, (f t (x t) - f t xstar)
      ≤ (G ^ 2 / (2 * α)) * (1 + Real.log T) := by
  have hα0 : α ≠ 0 := ne_of_gt hα
  have ht1 : ∀ t : ℕ, ((t : ℝ) + 1) ≠ 0 := by
    intro t
    have hnn : (0 : ℝ) ≤ (t : ℝ) := by positivity
    have hpos : (0 : ℝ) < (t : ℝ) + 1 := by linarith
    exact ne_of_gt hpos
  have h2α : (2 : ℝ) * α ≠ 0 := mul_ne_zero (by norm_num) hα0
  -- The scheduled step sizes are positive.
  have hη : ∀ t : ℕ, (0 : ℝ) < 1 / (α * ((t : ℝ) + 1)) := by
    intro t
    have hnn : (0 : ℝ) ≤ (t : ℝ) := by positivity
    have hpos : (0 : ℝ) < (t : ℝ) + 1 := by linarith
    exact div_pos zero_lt_one (mul_pos hα hpos)
  have hηnn : ∀ t : ℕ, (0 : ℝ) ≤ (1 / (α * ((t : ℝ) + 1))) / 2 :=
    fun t => (div_pos (hη t) two_pos).le
  have hg2 : ∀ t : ℕ, ‖g t (x t)‖ ^ 2 ≤ G ^ 2 :=
    fun t => pow_le_pow_left₀ (norm_nonneg _) (hG t) 2
  -- Per-round distance terms combine into a telescoping difference.
  have hcombine : ∀ t : ℕ,
      (‖x t - xstar‖ ^ 2 - ‖x (t + 1) - xstar‖ ^ 2)
        / (2 * (1 / (α * ((t : ℝ) + 1)))) - (α / 2) * ‖x t - xstar‖ ^ 2
        = (α / 2) * (((t : ℝ) * ‖x t - xstar‖ ^ 2)
          - (((t + 1 : ℕ) : ℝ) * ‖x (t + 1) - xstar‖ ^ 2)) := by
    intro t
    have ht1t := ht1 t
    have hmul : α * ((t : ℝ) + 1) ≠ 0 := mul_ne_zero hα0 ht1t
    have h2η : (2 : ℝ) * (1 / (α * ((t : ℝ) + 1))) ≠ 0 :=
      mul_ne_zero (by norm_num) (one_div_ne_zero hmul)
    rw [Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  -- Each round is bounded by a telescoping term plus a step term.
  have hround : ∀ t ∈ Finset.range T,
      f t (x t) - f t xstar
        ≤ (α / 2) * (((t : ℝ) * ‖x t - xstar‖ ^ 2)
            - (((t + 1 : ℕ) : ℝ) * ‖x (t + 1) - xstar‖ ^ 2))
          + ((1 / (α * ((t : ℝ) + 1))) / 2) * G ^ 2 := by
    intro t _
    have hL1 := ogd_strongly_convex_step proj f g α (1 / (α * ((t : ℝ) + 1)))
      x xstar t (hη t) hproj hprojstar (hupd t) (hsc t)
    have hS : ‖xstar - x t‖ = ‖x t - xstar‖ := by rw [← neg_sub, norm_neg]
    rw [hS, hcombine t] at hL1
    have hle := mul_le_mul_of_nonneg_left (hg2 t) (hηnn t)
    linarith
  -- Sum over rounds and split distance and step contributions.
  have hsum := Finset.sum_le_sum hround
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  -- The distance terms telescope.
  have htele : (∑ t ∈ Finset.range T, (((t : ℝ) * ‖x t - xstar‖ ^ 2)
      - (((t + 1 : ℕ) : ℝ) * ‖x (t + 1) - xstar‖ ^ 2)))
      = 0 - (T : ℝ) * ‖x T - xstar‖ ^ 2 := by
    have h0 :=
      Finset.sum_range_sub' (fun t : ℕ => (t : ℝ) * ‖x t - xstar‖ ^ 2) T
    simpa using h0
  rw [htele] at hsum
  -- The step terms factor through the harmonic sum.
  have hterm : ∀ t : ℕ, ((1 / (α * ((t : ℝ) + 1))) / 2) * G ^ 2
      = (G ^ 2 / (2 * α)) * ((1 : ℝ) / ((t : ℝ) + 1)) := by
    intro t
    have ht1t := ht1 t
    have hmul : α * ((t : ℝ) + 1) ≠ 0 := mul_ne_zero hα0 ht1t
    field_simp
  simp_rw [hterm] at hsum
  rw [← Finset.mul_sum] at hsum
  have hL2 := harmonic_sum_le_one_add_log T hT
  have hnnC : (0 : ℝ) ≤ G ^ 2 / (2 * α) :=
    div_nonneg (sq_nonneg G) (by linarith)
  have hstep_le := mul_le_mul_of_nonneg_left hL2 hnnC
  have hdist : (α / 2) * (0 - (T : ℝ) * ‖x T - xstar‖ ^ 2) ≤ 0 := by
    have hα2 : (0 : ℝ) < α / 2 := by linarith
    have hnn : (0 : ℝ) ≤ (T : ℝ) * ‖x T - xstar‖ ^ 2 := by positivity
    have h1 := mul_nonneg (le_of_lt hα2) hnn
    linarith
  calc ∑ t ∈ Finset.range T, (f t (x t) - f t xstar)
      ≤ (α / 2) * (0 - (T : ℝ) * ‖x T - xstar‖ ^ 2)
        + (G ^ 2 / (2 * α))
          * (∑ t ∈ Finset.range T, (1 : ℝ) / ((t : ℝ) + 1)) := hsum
    _ ≤ 0 + (G ^ 2 / (2 * α)) * (1 + Real.log T) :=
        add_le_add hdist hstep_le
    _ = (G ^ 2 / (2 * α)) * (1 + Real.log T) := zero_add _

/-- Varying-step online gradient descent iterates.

The existing `ogdIter` iterate at unit step with scaled round gradients
`fun t x => η t • g t x`, giving the projected-gradient recursion with
a step-size sequence `η` (see `ogdIterVarying_eq_ogdIter`).
-/
noncomputable def ogdIterVarying {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (proj : E → E) (g : ℕ → E → E) (η : ℕ → ℝ) (x0 : E) : ℕ → E :=
  ogdIter proj (fun t x => η t • g t x) 1 x0

/-- Successor equation for the varying-step iterates:
`x_{t+1} = proj (x_t - η_t • g_t x_t)`. -/
theorem ogdIterVarying_succ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (proj : E → E) (g : ℕ → E → E) (η : ℕ → ℝ) (x0 : E) (t : ℕ) :
    ogdIterVarying proj g η x0 (t + 1)
      = proj (ogdIterVarying proj g η x0 t - η t • g t (ogdIterVarying proj g η x0 t)) := by
  simp only [ogdIterVarying, ogdIter, one_smul]

/-- The varying-step iterates agree with the fixed-step `ogdIter` at unit
step with scaled round gradients, as functions. -/
theorem ogdIterVarying_eq_ogdIter {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (proj : E → E) (g : ℕ → E → E) (η : ℕ → ℝ) (x0 : E) :
    ogdIterVarying proj g η x0
      = ogdIter proj
        (fun t x => η t • g t x) 1 x0 := rfl

/-- Regret of the varying-step iterates for `α`-strongly convex losses.

Running `ogdIterVarying` with the schedule `η t = 1 / (α * (t + 1))`
enjoys the same regret bound as the abstract sequence in
`ogd_regret_strongly_convex`, from which this corollary follows directly.
Only the comparator instance of strong convexity along the iterates is
assumed.
-/
theorem ogdIterVarying_regret_strongly_convex {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (proj : E → E) (f : ℕ → E → ℝ) (g : ℕ → E → E) (α G : ℝ)
    (x0 : E) (xstar : E) (T : ℕ)
    (hα : 0 < α) (_hG0 : 0 ≤ G)
    (hproj : LipschitzWith 1 proj)
    (hprojstar : proj xstar = xstar)
    (hsc : ∀ t : ℕ, f t (ogdIterVarying proj g (fun t => 1 / (α * ((t : ℝ) + 1))) x0 t)
      + ⟪g t (ogdIterVarying proj g (fun t => 1 / (α * ((t : ℝ) + 1))) x0 t),
        xstar - ogdIterVarying proj g (fun t => 1 / (α * ((t : ℝ) + 1))) x0 t⟫_ℝ
      + (α / 2) * ‖xstar - ogdIterVarying proj g (fun t => 1 / (α * ((t : ℝ) + 1))) x0 t‖ ^ 2
      ≤ f t xstar)
    (hG : ∀ t, ‖g t (ogdIterVarying proj g (fun t => 1 / (α * ((t : ℝ) + 1))) x0 t)‖ ≤ G)
    (hT : 1 ≤ T) :
    ∑ t ∈ Finset.range T,
        (f t (ogdIterVarying proj g (fun t => 1 / (α * ((t : ℝ) + 1))) x0 t) - f t xstar)
      ≤ (G ^ 2 / (2 * α)) * (1 + Real.log T) := by
  exact ogd_regret_strongly_convex proj f g α G
    (ogdIterVarying proj g (fun t => 1 / (α * ((t : ℝ) + 1))) x0) xstar T
    hα _hG0 hproj hprojstar (fun t => ogdIterVarying_succ proj g _ x0 t) hsc hG hT

end MathlibExt.Analysis.Convex.OnlineGradientDescentStronglyConvex
