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
# Production sets and profit maximization

A price-taking firm chooses a net-output vector `y : ι → ℝ` from a production set
`Y : Set (ι → ℝ)`: positive entries are outputs, negative entries are inputs. At prices
`p : ι → ℝ` its profit is `p ⬝ᵥ y`. `IsProfitMax Y p y` says that `y` is feasible and that no
feasible plan earns more at `p`. No convexity, free disposal or sign condition on prices is
built in; results that need one state it.

This is the producer interface for the Atlas EC06 targets.

## Main definitions

* `MathlibExt.Economics.Producer.IsProfitMax`

## References

* A. Mas-Colell, M. D. Whinston, J. R. Green, *Microeconomic Theory*, Oxford University Press
  (1995), Section 5.B–5.C.
-/

@[expose] public section

namespace MathlibExt.Economics.Producer

/-- `y` maximizes profit at prices `p` over the production set `Y`: `y` is feasible and no
feasible net-output vector earns more profit `p ⬝ᵥ y'`. Price-taking is built in: profit is
linear in `y` at the given prices. -/
def IsProfitMax {ι : Type*} [Fintype ι] (Y : Set (ι → ℝ)) (p y : ι → ℝ) : Prop :=
  y ∈ Y ∧ ∀ y' ∈ Y, p ⬝ᵥ y' ≤ p ⬝ᵥ y

end MathlibExt.Economics.Producer
