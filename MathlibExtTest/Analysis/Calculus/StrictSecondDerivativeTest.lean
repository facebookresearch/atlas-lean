/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Calculus.StrictSecondDerivativeTest
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

namespace MetaMathlibExt

open Filter Topology

/-- `x ↦ x ^ 2` has second derivative `2 > 0` and vanishing first
derivative at `0`, so it has a strict local minimum there. -/
example : IsStrictLocalMin (fun x : ℝ => x ^ 2) 0 := by
  apply isStrictLocalMin_of_deriv_deriv_pos
  · have h1 : deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x := by
      funext x
      simp
    rw [h1]
    simp
  · simp
  · fun_prop

/-- `x ↦ -x ^ 2` has second derivative `-2 < 0` and vanishing first
derivative at `0`, so it has a strict local maximum there. -/
example : IsStrictLocalMax (fun x : ℝ => -x ^ 2) 0 := by
  apply isStrictLocalMax_of_deriv_deriv_neg
  · have h1 : deriv (fun x : ℝ => -x ^ 2) = fun x => -(2 * x) := by
      funext x
      simp
    rw [h1]
    simp
  · simp
  · fun_prop

/-- The strict local minimum of `x ↦ x ^ 2` at `0` is a local minimum in
Mathlib's non-strict sense, via the bridge lemma. -/
example : IsLocalMin (fun x : ℝ => x ^ 2) 0 :=
  (isStrictLocalMin_of_deriv_deriv_pos (f := fun x : ℝ => x ^ 2) (x₀ := 0)
    (by
      have h1 : deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x := by
        funext x
        simp
      rw [h1]
      simp)
    (by simp) (by fun_prop)).isLocalMin

/-- Strictness is genuine: at a strict local minimum the value is
*strictly* below nearby values, here `0 < x ^ 2` for `x ≠ 0` near `0`. -/
example : ∀ᶠ x in 𝓝[≠] (0 : ℝ), (0 : ℝ) < x ^ 2 := by
  have h := isStrictLocalMin_of_deriv_deriv_pos (f := fun x : ℝ => x ^ 2) (x₀ := 0)
    (by
      have h1 : deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x := by
        funext x
        simp
      rw [h1]
      simp)
    (by simp) (by fun_prop)
  simpa [IsStrictLocalMin] using h

/-- `x ↦ x ^ 3` is not a strict local minimum at `0`: it takes negative
values arbitrarily close to `0` (at `-δ / 2` for any `δ > 0`), while a
strict local minimum would force positivity there. -/
example : ¬ IsStrictLocalMin (fun x : ℝ => x ^ 3) 0 := by
  intro h
  have h' : ∀ᶠ x in 𝓝[≠] (0 : ℝ),
      (fun x : ℝ => x ^ 3) 0 < (fun x : ℝ => x ^ 3) x := h
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h'
  obtain ⟨δ, hδ, hδ'⟩ := h'
  have h1 : (0 : ℝ) < (-(δ / 2)) ^ 3 := by
    have htop := hδ' (y := -(δ / 2))
      (by
        rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (half_pos hδ)]
        exact half_lt_self hδ)
      (by simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith)
    simpa using htop
  have h2 : (-(δ / 2) : ℝ) ^ 3 < 0 := by
    rw [show (-(δ / 2) : ℝ) ^ 3 = -((δ / 2) ^ 3) by ring]
    simp [pow_pos (half_pos hδ) 3]
  linarith

end MetaMathlibExt
