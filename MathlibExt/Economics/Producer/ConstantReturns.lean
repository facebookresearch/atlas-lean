/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Producer.ProductionSet
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Constant returns to scale and zero maximal profit

A production set has constant returns to scale when every feasible plan may be scaled by any
nonnegative factor; the factor `0` makes inaction feasible. If profit attains a maximum at
prices `p`, that maximal profit is zero, so no feasible plan earns positive profit at `p`.

## Main results

* `MathlibExt.Economics.Producer.IsProfitMax.dotProduct_eq_zero_of_hasConstantReturns`
* `MathlibExt.Economics.Producer.IsProfitMax.dotProduct_nonpos_of_hasConstantReturns`

## References

* A. Mas-Colell, M. D. Whinston, J. R. Green, *Microeconomic Theory*, Oxford University Press
  (1995), Sections 5.B–5.C.

Atlas roadmap target EC06.T04.
-/

@[expose] public section

namespace MathlibExt.Economics.Producer

/-- Constant returns to scale: every feasible net-output vector may be scaled by any
nonnegative factor. The factor `0` makes inaction (zero production) feasible whenever `Y` is
nonempty. -/
def HasConstantReturns {ι : Type*} (Y : Set (ι → ℝ)) : Prop :=
  ∀ y ∈ Y, ∀ t : ℝ, 0 ≤ t → t • y ∈ Y

/-- **Zero profit under constant returns.** An attained (finite) maximum profit of a
constant-returns technology is zero. -/
theorem IsProfitMax.dotProduct_eq_zero_of_hasConstantReturns {ι : Type*} [Fintype ι]
    {Y : Set (ι → ℝ)} {p y : ι → ℝ} (hY : HasConstantReturns Y) (h : IsProfitMax Y p y) :
    p ⬝ᵥ y = 0 := by
  obtain ⟨hy, hmax⟩ := h
  have h2 := hmax (2 • y) (hY y hy 2 (by norm_num))
  have h0 := hmax (0 • y) (hY y hy 0 le_rfl)
  simp only [dotProduct_smul, smul_eq_mul] at h2
  simp only [zero_smul, dotProduct_zero] at h0
  linarith

/-- Under constant returns, if a maximum is attained at `p`, then no feasible plan earns
positive profit at `p`. -/
theorem IsProfitMax.dotProduct_nonpos_of_hasConstantReturns {ι : Type*} [Fintype ι]
    {Y : Set (ι → ℝ)} {p y : ι → ℝ} (hY : HasConstantReturns Y) (h : IsProfitMax Y p y) :
    ∀ z ∈ Y, p ⬝ᵥ z ≤ 0 := by
  intro z hz
  have heq := IsProfitMax.dotProduct_eq_zero_of_hasConstantReturns hY h
  calc p ⬝ᵥ z ≤ p ⬝ᵥ y := h.2 z hz
    _ = 0 := heq

end MathlibExt.Economics.Producer
