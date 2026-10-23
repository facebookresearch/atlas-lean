/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.HellySelection

@[expose] public section

open Filter ProbabilityTheory Set
open scoped Topology

namespace MathlibExtTest.Probability.HellySelection

/-- The step function at `c` — `0` before `c`, `1` from `c` on — is a
distribution function: the cumulative distribution function of a point mass
at `c`. -/
private theorem step_isDistributionFunction (c : ℝ) :
    IsDistributionFunction (fun x => if x < c then (0 : ℝ) else 1) where
  mono := by
    intro a b hab
    by_cases ha : a < c
    · by_cases hb : b < c
      · simp [ha, hb]
      · simp [ha, hb]
    · by_cases hb : b < c
      · exact absurd (lt_of_le_of_lt hab hb) ha
      · simp [ha, hb]
  right_continuous := by
    intro x
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    by_cases hx : x < c
    · refine ⟨c - x, sub_pos.mpr hx, fun y hy hyx => ?_⟩
      have hy_lt : y < c := by
        have h1 := hyx
        rw [Real.dist_eq, abs_lt] at h1
        linarith [h1.2]
      rw [ite_eq_left hy_lt, ite_eq_left hx]
      simp [hε]
    · push Not at hx
      refine ⟨1, one_pos, fun y hy _hyx => ?_⟩
      have hy_ge : c ≤ y := le_trans hx (Set.mem_Ici.mp hy)
      rw [ite_eq_right (not_lt.mpr hy_ge), ite_eq_right (not_lt.mpr hx)]
      simp [hε]
  tendsto_atBot := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_atBot.mpr ⟨c - 1, fun _ h => h⟩] with y hy
    show (0 : ℝ) = if y < c then (0 : ℝ) else 1
    rw [ite_eq_left (lt_of_le_of_lt hy (by linarith))]
  tendsto_atTop := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_atTop.mpr ⟨c + 1, fun _ h => h⟩] with y hy
    show (1 : ℝ) = if y < c then (0 : ℝ) else 1
    rw [ite_eq_right (not_lt.mpr (le_trans (by linarith) hy))]

/-- Helly's selection theorem restates with the exact public signature. -/
example (F : ℕ → ℝ → ℝ) (hF : ∀ n, IsDistributionFunction (F n)) :
    ∃ (φ : ℕ → ℕ) (G : HellySelection.MonotoneRightContinuous),
      StrictMono φ ∧
      ∀ x, ContinuousAt (↑G) x → Tendsto (fun k => F (φ k) x) atTop (𝓝 (G x)) :=
  helly_selection F hF

/-- The step distribution function is non-negative and bounded by `1`. -/
example (c x : ℝ) : 0 ≤ (if x < c then (0 : ℝ) else 1) ∧
    (if x < c then (0 : ℝ) else 1) ≤ 1 := by
  have h := step_isDistributionFunction c
  exact ⟨h.nonneg x, h.le_one x⟩

/-- Helly's theorem applied to the constant sequence of point-mass
distribution functions: a convergent subsequence exists. -/
example :
    ∃ (φ : ℕ → ℕ) (G : HellySelection.MonotoneRightContinuous),
      StrictMono φ ∧
      ∀ x, ContinuousAt (↑G) x →
        Tendsto (fun k => (fun _ => if x < (0 : ℝ) then (0 : ℝ) else 1) (φ k))
          atTop (𝓝 (G x)) :=
  helly_selection _ (fun _ => step_isDistributionFunction 0)

/-- Helly's theorem applied to the genuinely non-constant sequence of
point masses at `n`: the mass escapes to `+∞`, so the subsequential limit
is allowed to lose mass — the theorem still produces a monotone,
right-continuous subsequential limit. -/
example :
    ∃ (φ : ℕ → ℕ) (G : HellySelection.MonotoneRightContinuous),
      StrictMono φ ∧
      ∀ x, ContinuousAt (↑G) x →
        Tendsto (fun k => (if x < (φ k : ℝ) then (0 : ℝ) else 1))
          atTop (𝓝 (G x)) := by
  apply helly_selection (fun n => fun x => if x < (n : ℝ) then (0 : ℝ) else 1)
  intro n
  exact step_isDistributionFunction (n : ℝ)

-- `#print axioms` for the public declarations: only the standard triple.
#print axioms ProbabilityTheory.IsDistributionFunction
#print axioms ProbabilityTheory.HellySelection.MonotoneRightContinuous
#print axioms ProbabilityTheory.HellySelection.MonotoneRightContinuous.instCoeFun
#print axioms ProbabilityTheory.helly_selection
#print axioms ProbabilityTheory.IsDistributionFunction.nonneg
#print axioms ProbabilityTheory.IsDistributionFunction.le_one
#print axioms ProbabilityTheory.IsDistributionFunction.mem_Icc
#print axioms ProbabilityTheory.HellySelection.ofMonotone

end MathlibExtTest.Probability.HellySelection
