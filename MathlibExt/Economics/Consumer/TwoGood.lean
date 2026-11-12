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
# The two-good consumer problem

Minimal interface for worked consumer-choice examples: the budget set, Marshallian
(utility-maximizing) demand, and the nonnegative orthant of two goods.

## Main definitions

* `budgetSet X p w`: bundles `x ∈ X` with `p ⬝ᵥ x ≤ w`.
* `IsMarshallianDemand u X p w x`: `x` is affordable and maximizes `u` over the budget set.
* `twoGoodSet`: the consumption set `{x : Fin 2 → ℝ | 0 ≤ x 0 ∧ 0 ≤ x 1}`.

The definitions have the same shape as the general consumer-duality interface under review in
Atlas (`Economics.Consumer` in `MathlibExt/Economics/Consumer/ExpenditureDuality.lean`, roadmap
EC04.T02); they should be unified with it once that lands.

Atlas roadmap module EC03 (worked demand models).

## References

* A. Mas-Colell, M. D. Whinston and J. R. Green, *Microeconomic Theory*, Oxford University
  Press (1995), chs. 2–3.
-/

@[expose] public section

namespace MathlibExt.Economics.Consumer

open Matrix

/-- The budget set `B(p, w) = {x ∈ X | p ⬝ᵥ x ≤ w}`: affordable consumption
bundles in the consumption set `X` at prices `p` and wealth `w`. -/
def budgetSet {ι : Type*} [Fintype ι] (X : Set (ι → ℝ)) (p : ι → ℝ) (w : ℝ) :
    Set (ι → ℝ) :=
  {x | x ∈ X ∧ p ⬝ᵥ x ≤ w}

/-- `x` is a Marshallian (utility-maximizing) demand at `(p, w)`: it is
affordable and no affordable bundle gives strictly higher utility. -/
def IsMarshallianDemand {ι : Type*} [Fintype ι] (u : (ι → ℝ) → ℝ)
    (X : Set (ι → ℝ)) (p : ι → ℝ) (w : ℝ) (x : ι → ℝ) : Prop :=
  x ∈ budgetSet X p w ∧ ∀ y ∈ budgetSet X p w, u y ≤ u x

/-- The two-good consumption set: the nonnegative orthant of `Fin 2 → ℝ`. -/
def twoGoodSet : Set (Fin 2 → ℝ) :=
  {x | ∀ i, 0 ≤ x i}

end MathlibExt.Economics.Consumer
