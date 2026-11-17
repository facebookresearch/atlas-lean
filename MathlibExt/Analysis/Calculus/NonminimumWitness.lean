/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Negative tangent direction as a nonminimum witness

## i. Overview

If `g(t) = Pi (x0 + t v)` is continuous at `0` with `g'(0) = 0` and
`g''(0) < 0`, then `x0` is not a local minimum of `Pi` along the
admissible line: arbitrarily close points on the line have strictly
lower potential.

## ii. Key results

- `NonminimumWitness.exists_lower_arbitrarily_close`: lower points
  arbitrarily close.
- `NonminimumWitness.not_forall_le_line`: not a line minimum.

## iii. Table of contents

- A. Nonminimum witness

## iv. References

- Standard second-order necessary conditions for minima in
  variational calculus / optimization.

## A. Nonminimum witness
-/

@[expose] public section

namespace NonminimumWitness

/-- Helper: zero first derivative and negative second derivative at `0`
give strictly lower values immediately to the right of `0`. -/
theorem exists_pos_lower (g : ℝ → ℝ)
    (hc : ContinuousAt g 0)
    (hg0 : deriv g 0 = 0)
    (hg2 : deriv (deriv g) 0 < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ → g s < g 0 := by
  have hdiff : DifferentiableAt ℝ (deriv g) 0 :=
    differentiableAt_of_deriv_ne_zero (ne_of_lt hg2)
  have htend := hdiff.hasDerivAt.tendsto_slope
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ, slope (deriv g) 0 t < 0 :=
    htend.eventually_lt_const hg2
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at hev
  obtain ⟨δ, hδpos, hδ⟩ := hev
  have hneg : ∀ t : ℝ, 0 < t → t < δ → deriv g t < 0 := by
    intro t ht0 htδ
    have hdist : dist t 0 < δ := by
      rw [dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_pos ht0]
      exact htδ
    have htne : t ∈ ({0}ᶜ : Set ℝ) := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt ht0
    have hslope := hδ t (Metric.mem_ball.mpr hdist) htne
    rw [slope_def_field, hg0, sub_zero, sub_zero] at hslope
    rcases div_neg_iff.mp hslope with ⟨-, hcon⟩ | ⟨hlt, -⟩
    · exact absurd hcon (not_lt_of_gt ht0)
    · exact hlt
  have hδ2pos : 0 < δ / 2 := by linarith
  have hcont : ContinuousOn g (Set.Icc 0 (δ / 2)) := by
    intro x hx
    rcases eq_or_ne x 0 with rfl | hne
    · exact hc.continuousWithinAt
    · have hx0 : 0 < x := lt_of_le_of_ne' hx.1 hne
      have hxδ : x < δ := lt_of_le_of_lt hx.2 (by linarith)
      have hne0 : deriv g x ≠ 0 := ne_of_lt (hneg x hx0 hxδ)
      exact (differentiableAt_of_deriv_ne_zero hne0).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn g (Set.Icc 0 (δ / 2)) :=
    strictAntiOn_of_deriv_neg (convex_Icc 0 (δ / 2)) hcont (by
      intro x hx
      rw [interior_Icc] at hx
      exact hneg x hx.1 (lt_of_lt_of_le hx.2 (by linarith)))
  refine ⟨δ / 2, hδ2pos, fun s hs0 hsδ => ?_⟩
  exact hanti ⟨le_refl 0, le_of_lt hδ2pos⟩ ⟨hs0.le, hsδ.le⟩ hs0

/-- Negative second derivative along an admissible line excludes a
local minimum: if `g(t) = Pi (x0 + t v)` has `g'(0) = 0` and
`g''(0) < 0` (with `v ≠ 0`), then arbitrarily close to `x0` along the
line there are admissible points with strictly lower potential. -/
theorem exists_lower_arbitrarily_close {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Pi : E → ℝ) (x0 v : E) (hv : v ≠ 0)
    (hc : ContinuousAt (fun t : ℝ => Pi (x0 + t • v)) 0)
    (hg0 : deriv (fun t : ℝ => Pi (x0 + t • v)) 0 = 0)
    (hg2 : deriv (deriv (fun t : ℝ => Pi (x0 + t • v))) 0 < 0) :
    ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, t ≠ 0 ∧ |t| * ‖v‖ < ε
      ∧ Pi (x0 + t • v) < Pi x0 := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_pos_lower (fun t : ℝ => Pi (x0 + t • v)) hc hg0 hg2
  intro ε hε
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h2v : 0 < (2 : ℝ) * ‖v‖ := mul_pos two_pos hvnorm
  set s : ℝ := min (δ / 2) (ε / (2 * ‖v‖)) with hs
  have hspos : 0 < s := by
    rw [hs]
    exact lt_min_iff.mpr ⟨by linarith, div_pos hε h2v⟩
  have hsδ : s < δ := by
    rw [hs]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hsmul : s * ‖v‖ < ε := by
    have hvn : ‖v‖ ≠ 0 := ne_of_gt hvnorm
    have h2vne : (2 : ℝ) * ‖v‖ ≠ 0 := mul_ne_zero two_ne_zero hvn
    rw [hs]
    calc min (δ / 2) (ε / (2 * ‖v‖)) * ‖v‖
        ≤ (ε / (2 * ‖v‖)) * ‖v‖ :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hvnorm.le
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  refine ⟨s, ne_of_gt hspos, ?_, ?_⟩
  · rw [abs_of_pos hspos]
    exact hsmul
  · have hlt := hδ s hspos hsδ
    simpa using hlt

/-- In particular, `Pi x0` is not a lower bound for `Pi` on the line. -/
theorem not_forall_le_line {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Pi : E → ℝ) (x0 v : E) (hv : v ≠ 0)
    (hc : ContinuousAt (fun t : ℝ => Pi (x0 + t • v)) 0)
    (hg0 : deriv (fun t : ℝ => Pi (x0 + t • v)) 0 = 0)
    (hg2 : deriv (deriv (fun t : ℝ => Pi (x0 + t • v))) 0 < 0) :
    ¬ ∀ t : ℝ, Pi (x0 : E) ≤ Pi (x0 + t • v) := by
  intro hall
  obtain ⟨t, -, -, hlt⟩ := exists_lower_arbitrarily_close Pi x0 v hv hc hg0 hg2 1 one_pos
  exact absurd (hall t) (not_le_of_gt hlt)

end NonminimumWitness
