/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellGaussBonnetLocal

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellGaussBonnet`

Instantiates the local cell Gauss–Bonnet identity `localIdentity_corrected` at the configuration
that refutes the uncorrected identity (only the south-west diagonal neighbour present), computes
both sides there, and checks the counterexample lemmas `cornerDiff_cex`, `eulerChar_cex`,
`gaussBonnet_stated_false` and `localIdentity_stated_false`.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellGaussBonnet

open StatMech.Onsager.CellGaussBonnet

-- With only the south-west neighbour present the corner defect jumps by `2`.
example : lhsLocal false false false false false false false true = 2 := by decide

-- Four times the Euler change is `0` there, and the pinch change is `1`.
example : rhsStated false false false false false false false true = 0 ∧
    pinchDelta false false false false false false false true = 1 := by
  decide

-- Non-vacuity of `localIdentity_corrected` at that configuration.
example : lhsLocal false false false false false false false true
    = rhsCorrected false false false false false false false true :=
  localIdentity_corrected _ _ _ _ _ _ _ _

-- At an isolated new cell both sides equal `4`.
example : lhsLocal false false false false false false false false = 4 ∧
    rhsCorrected false false false false false false false false = 4 := by
  decide

-- Filling the hole of a `3 × 3` annulus (all eight neighbours present): four reflex corners become
-- interior (`+4`), and the Euler characteristic rises from `0` to `1` (`4 * 1`).
example : lhsLocal true true true true true true true true = 4 ∧
    rhsCorrected true true true true true true true true = 4 := by
  decide

-- The uncorrected global formula is refuted.
example : ¬ ∀ S : Finset (ℤ × ℤ), StatMech.Onsager.CellEuler.cornerDiff S =
    4 * StatMech.Onsager.CellEuler.eulerChar S :=
  gaussBonnet_stated_false

-- The uncorrected local formula is refuted.
example : ¬ ∀ e w n s ne nw se sw : Bool,
    lhsLocal e w n s ne nw se sw = rhsStated e w n s ne nw se sw :=
  localIdentity_stated_false

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.TurningNumber.CellGaussBonnet
