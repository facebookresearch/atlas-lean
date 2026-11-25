/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.PeierlsSquareLattice

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.PeierlsOuterContour`

* `spinCompatibleFill_outerContourMap` discharges the hypothesis `OuterContourMap n` of the
  outer-contour lemmas in every box, so `poc_probOriginMinus_le_two_peierls` gives the uniform
  Peierls bound: once `peierlsRatio 2 β < 1`, the origin is minus with probability at most
  `twoPeierlsBound 2 β` in every box.
* `poc_peierls_long_range_order` applies too, but its conclusion
  `plusMeasure 2 n β 0 ≠ minusMeasure 2 n β 0` is weak: the plus and minus box measures fix
  opposite spins outside `Λ_n`, so they always differ.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.PeierlsOuterContour

open _root_.StatMech _root_.StatMech.Ising _root_.StatMech.Lattice

/-- The outer-contour Peierls bound holds in every box, uniformly in `n`. -/
example (n : ℕ) (β : ℝ) (hx : peierlsRatio 2 β < 1) :
    probOriginMinus (plusField 2) n (bondFinsetTouch 2 n) β 0 ≤ twoPeierlsBound 2 β :=
  poc_probOriginMinus_le_two_peierls n β hx (spinCompatibleFill_outerContourMap n)

/-- `poc_peierls_long_range_order` applies with no further hypothesis. Its conclusion is a weak
form of long-range order, as the plus and minus box measures fix opposite spins outside `Λ_n`; the
informative statement is the uniform bound above. -/
example : ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
    plusMeasure 2 n β 0 ≠ minusMeasure 2 n β 0 :=
  poc_peierls_long_range_order spinCompatibleFill_outerContourMap

end PhyslibExtTest.CondensedMatter.IsingModel.PeierlsOuterContour
