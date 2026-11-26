/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.HolleyFKG

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.HolleyFKG`

* Holley's inequality on `Bool` for the point masses at `⊥ = false` and `⊤ = true` (Holley's lattice
  condition holds), giving `δ_false ≤_st δ_true`, and a monotone coupling.
* The FKG inequality on `Bool` for the fair weight and `f = g = (b ↦ if b then 1 else 0)`.
* `restrictTo` evaluates as expected.
-/

@[expose] public section

open scoped NNReal
open StatMech.Probability

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.HolleyFKG

/-- The point mass at `false`. -/
def δF : Bool → ℝ≥0 := fun b => if b then 0 else 1
/-- The point mass at `true`. -/
def δT : Bool → ℝ≥0 := fun b => if b then 1 else 0

theorem holley_FT : HolleyLatticeCondition δF δT := by
  intro x y; cases x <;> cases y <;> simp [δF, δT]

theorem sum_FT : ∑ a, δF a = ∑ a, δT a := by simp [δF, δT]

example : StochasticDom δF δT := holley_domination sum_FT holley_FT

example : ∃ π : Bool × Bool → ℝ≥0, IsMonotoneCoupling δF δT π :=
  holley_exists_isMonotoneCoupling sum_FT holley_FT

theorem mono_ind : Monotone (fun b : Bool => if b then (1 : ℝ) else 0) := by
  intro a b h
  cases a <;> cases b <;> first | exact absurd h (by decide) | simp

example : (∑ a : Bool, (1 / 2 : ℝ) * (if a then 1 else 0))
      * (∑ a : Bool, (1 / 2 : ℝ) * (if a then 1 else 0))
    ≤ ∑ a : Bool, (1 / 2 : ℝ) * ((if a then 1 else 0) * (if a then 1 else 0)) :=
  fkg_inequality (π := fun _ => 1 / 2) (fun _ => by norm_num) (by norm_num)
    (fun _ _ => le_rfl) mono_ind mono_ind

example : restrictTo δT {false} true = 0 := by simp [restrictTo]

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.HolleyFKG
