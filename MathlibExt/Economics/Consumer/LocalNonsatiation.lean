/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Local nonsatiation

A utility `u : (ι → ℝ) → ℝ` on bundles of finitely many goods is locally nonsatiated on a
consumption set `X` if arbitrarily close to every bundle in `X` there is a bundle in `X` with
strictly higher utility (Mas-Colell–Whinston–Green, Def. 3.B.3). Distance is the sup distance on
`ι → ℝ`.

This is the single definition shared by the consumer-theory files (`X` arbitrary) and the second
welfare theorem (`X = ℝ^L_+`, see `MathlibExt.Economics.SecondWelfareTheorem.LocallyNonsatiated`).

## Main definitions

* `MathlibExt.Economics.Consumer.LocallyNonsatiated`: local nonsatiation of `u` on `X`.

## References

* A. Mas-Colell, M. D. Whinston, J. R. Green, *Microeconomic Theory*, Oxford University Press
  (1995), Definition 3.B.3.
-/

@[expose] public section

namespace MathlibExt.Economics.Consumer

/-- Local nonsatiation of `u` on `X` (MWG Def. 3.B.3): every neighborhood of every bundle in `X`
contains a bundle in `X` with strictly higher utility. Distance is the sup distance on
`ι → ℝ`. -/
def LocallyNonsatiated {ι : Type*} [Fintype ι] (u : (ι → ℝ) → ℝ)
    (X : Set (ι → ℝ)) : Prop :=
  ∀ x ∈ X, ∀ ε > 0, ∃ y ∈ X, dist y x < ε ∧ u x < u y

end MathlibExt.Economics.Consumer
