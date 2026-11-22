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
import MathlibExt.Analysis.Calculus.StrictSecondDerivativeTest
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
  have hmax : IsStrictLocalMax (fun t : ℝ => Pi (x0 + t • v)) 0 :=
    isStrictLocalMax_of_deriv_deriv_neg hg2 hg0 hc
  simp only [IsStrictLocalMax, eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hmax
  obtain ⟨δ, hδ, hlt⟩ := hmax
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  intro ε hε
  have h2v : (0 : ℝ) < 2 * ‖v‖ := mul_pos (by norm_num) hvnorm
  have h2vne : (2 : ℝ) * ‖v‖ ≠ 0 := ne_of_gt h2v
  set s : ℝ := min (δ / 2) (ε / (2 * ‖v‖)) with hs
  have hsδ : s ≤ δ / 2 := min_le_left _ _
  have hsε : s ≤ ε / (2 * ‖v‖) := min_le_right _ _
  have hspos : 0 < s := by
    rw [hs]
    exact lt_min (by linarith) (div_pos hε h2v)
  have hmem : s ∈ ({0} : Set ℝ)ᶜ := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt hspos
  have hdist : dist s 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hspos]
    linarith
  have h := hlt hdist hmem
  simp only [zero_smul, add_zero] at h
  refine ⟨s, ne_of_gt hspos, ?_, h⟩
  rw [abs_of_pos hspos]
  calc s * ‖v‖ ≤ (ε / (2 * ‖v‖)) * ‖v‖ :=
          mul_le_mul_of_nonneg_right hsε (norm_nonneg _)
      _ = ε / 2 := by
          field_simp
      _ < ε := by linarith

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
