/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.SemilinearFlow.Interface

open MathlibExt.Analysis.PDE.SemilinearFlow MeasureTheory Set
open scoped NNReal

/-- The trivial semigroup `S t = 1` on `ℝ`. -/
noncomputable def trivialSemigroup : ℝ≥0 → ℝ →L[ℝ] ℝ := fun _ => 1

theorem isC0Semigroup_trivial : IsC0Semigroup trivialSemigroup :=
  ⟨rfl, fun _ _ => by simp [trivialSemigroup, ContinuousLinearMap.one_def],
    fun _ => continuous_const,
    fun _ => ⟨1, fun _ _ => by simp [trivialSemigroup]⟩⟩

-- Bounded generators give C₀ semigroups; `A = 0` recovers the trivial semigroup.
example : IsC0Semigroup fun t : ℝ≥0 => NormedSpace.exp ((t : ℝ) • (0 : ℝ →L[ℝ] ℝ)) :=
  isC0Semigroup_exp 0

example : (fun t : ℝ≥0 => NormedSpace.exp ((t : ℝ) • (0 : ℝ →L[ℝ] ℝ))) = trivialSemigroup := by
  funext t; simp [trivialSemigroup]

-- A C₀ semigroup is jointly continuous.
example : Continuous fun p : ℝ≥0 × ℝ => trivialSemigroup p.1 p.2 :=
  isC0Semigroup_trivial.continuous_uncurry

-- The Duhamel term of a zero forcing vanishes, and that of a unit forcing under `S = 1` is `t`.
example (t : ℝ) : duhamel trivialSemigroup (fun _ => (0 : ℝ)) t = 0 := by simp [duhamel]

theorem duhamel_trivial_one (t : ℝ) : duhamel trivialSemigroup (fun _ => (1 : ℝ)) t = t := by
  simp [duhamel, trivialSemigroup]

example : Continuous (duhamel trivialSemigroup fun s => s) :=
  isC0Semigroup_trivial.continuous_duhamel continuous_id

-- A non-vacuous mild solution: `u' = 1`, `u 0 = 0` has the mild solution `u t = t`.
theorem isMildSolution_id : IsMildSolution trivialSemigroup (fun _ => (1 : ℝ)) 0 1 id :=
  ⟨continuous_id.continuousOn, fun t _ => by simp [duhamel_trivial_one]⟩

example : (id : ℝ → ℝ) 0 = 0 :=
  isMildSolution_id.apply_zero isC0Semigroup_trivial zero_le_one

-- Lipschitz-on-balls hypotheses for constant and linear reactions.
theorem lipschitz_const : ∀ R : ℝ, ∃ L : ℝ≥0,
    LipschitzOnWith L (fun _ : ℝ => (1 : ℝ)) (Metric.closedBall 0 R) :=
  fun _ => ⟨0, (LipschitzWith.const _).lipschitzOnWith⟩

theorem lipschitz_id : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L (id : ℝ → ℝ) (Metric.closedBall 0 R) :=
  fun _ => ⟨1, LipschitzWith.id.lipschitzOnWith⟩

example : Continuous (fun _ : ℝ => (1 : ℝ)) :=
  continuous_of_lipschitzOnWith_closedBall lipschitz_const

-- Local existence: `u' = u` has a mild solution from every initial value in `[-5, 5]`, on a
-- common time interval.
example : ∃ T > 0, ∀ x₀ : ℝ, ‖x₀‖ ≤ 5 →
    ∃ u : ℝ → ℝ, Continuous u ∧ IsMildSolution trivialSemigroup id x₀ T u :=
  exists_isMildSolution isC0Semigroup_trivial lipschitz_id 5

-- Uniqueness identifies every mild solution of `u' = 1`, `u 0 = 0` on `[0, 1]` with `t ↦ t`.
example (v : ℝ → ℝ) (hv : IsMildSolution trivialSemigroup (fun _ => (1 : ℝ)) 0 1 v) :
    EqOn v id (Icc 0 1) :=
  hv.eqOn isC0Semigroup_trivial lipschitz_const isMildSolution_id

-- Boundary case `T < 0`: the time interval is empty, so uniqueness is vacuous but still holds.
example (u v : ℝ → ℝ) (hu : IsMildSolution trivialSemigroup id 0 (-1) u)
    (hv : IsMildSolution trivialSemigroup id 0 (-1) v) : EqOn u v (Icc 0 (-1)) :=
  hu.eqOn isC0Semigroup_trivial lipschitz_id hv

-- Lipschitz dependence on initial data.
example (u v : ℝ → ℝ) (hu : IsMildSolution trivialSemigroup id 1 1 u)
    (hv : IsMildSolution trivialSemigroup id 2 1 v) :
    ∃ C, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) 1, ‖u t - v t‖ ≤ C * ‖(1 : ℝ) - 2‖ :=
  hu.exists_norm_sub_le isC0Semigroup_trivial lipschitz_id hv

-- Incompatible spaces: the quadratic reaction does not act on `L²(0, 1)`.
example : ∃ u : ℝ → ℝ, MemLp u 2 (volume.restrict (Ioo 0 1)) ∧
    ¬ MemLp (fun x => u x ^ 2) 2 (volume.restrict (Ioo 0 1)) :=
  exists_memLp_two_not_memLp_two_sq
