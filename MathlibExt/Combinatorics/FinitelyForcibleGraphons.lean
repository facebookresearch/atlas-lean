/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Graphons

`IsGraphon` specifies joint measurability, symmetry and the range of a kernel on the real plane.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.FinitelyForcibleOptimumOWR4212Problem011Wanted

/-- **Graphon.** A graphon is a function $W$ of two real variables that is jointly measurable
(measurable as a function on $\mathbb{R}^2$), symmetric ($W(x, y) = W(y, x)$ for all real $x, y$)
and takes values in $[0, 1]$ at every point of $\mathbb{R}^2$.

Only the values of $W$ on $[0, 1]^2$ enter the densities. -/
def IsGraphon (W : ℝ → ℝ → ℝ) : Prop :=
  Measurable (Function.uncurry W) ∧ (∀ x y, W x y = W y x) ∧ ∀ x y, W x y ∈ Set.Icc (0 : ℝ) 1

end MathlibExt.Combinatorics.FinitelyForcibleOptimumOWR4212Problem011Wanted
