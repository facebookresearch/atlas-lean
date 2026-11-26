/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.StochasticOrder.StrassenFiniteCoupling

/-!
# Tests for `MathlibExt.Probability.StochasticOrder.StrassenFiniteCoupling`

* On the two-point chain `Bool` (`false < true`): the point mass at `false` is dominated by the
  point mass at `true`, through the explicit monotone coupling concentrated on `(false, true)`
  (`StochasticDom.of_isMonotoneCoupling`), and `strassen_finite` recovers a coupling.
-/

@[expose] public section

open StatMech.Probability
open scoped NNReal

namespace MathlibExtTest.StatMech.Probability.StochasticOrder.StrassenFiniteCoupling

/-- The point mass at `b` on `Bool`. -/
def pt (b : Bool) : Bool → ℝ≥0 := fun x => if x = b then 1 else 0

/-- The coupling concentrated on `(false, true)`. -/
def π₀ : Bool × Bool → ℝ≥0 := fun p => if p = (false, true) then 1 else 0

lemma isMonotoneCoupling_π₀ : IsMonotoneCoupling (pt false) (pt true) π₀ where
  fst_marginal x := by cases x <;> simp [pt, π₀]
  snd_marginal y := by cases y <;> simp [pt, π₀]
  supported x y h := by
    cases x <;> cases y <;> simp_all [π₀]

example : StochasticDom (pt false) (pt true) :=
  StochasticDom.of_isMonotoneCoupling isMonotoneCoupling_π₀

example : ∃ π : Bool × Bool → ℝ≥0, IsMonotoneCoupling (pt false) (pt true) π :=
  (strassen_finite (by simp [pt])).mp (StochasticDom.of_isMonotoneCoupling isMonotoneCoupling_π₀)

end MathlibExtTest.StatMech.Probability.StochasticOrder.StrassenFiniteCoupling
