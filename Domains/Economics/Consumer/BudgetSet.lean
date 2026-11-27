/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul

/-!
# Consumer budget sets

The shared budget-set definition for consumer demand and expenditure duality.
-/

@[expose] public section

namespace MathlibExt.Economics.Consumer

open Matrix

/-- The budget set `B(p, w) = {x ∈ X | p ⬝ᵥ x ≤ w}`: affordable consumption
bundles in the consumption set `X` at prices `p` and wealth `w`. -/
def budgetSet {ι : Type*} [Fintype ι] (X : Set (ι → ℝ)) (p : ι → ℝ) (w : ℝ) :
    Set (ι → ℝ) :=
  {x | x ∈ X ∧ p ⬝ᵥ x ≤ w}

end MathlibExt.Economics.Consumer
