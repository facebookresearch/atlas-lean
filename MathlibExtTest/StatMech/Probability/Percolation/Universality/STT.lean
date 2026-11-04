/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.STT

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.STT`

* Criticality functions at small inputs; `(1/2, 1/2, 0)` is on the triangular critical surface and
  `(1/2, 1/2)` on the square one.
* The star–triangle transformation `starTriangle_connectivity` at the critical point
  `(1/2, 1/2, 0)`; off the critical surface (`p = (1/2, 1/2, 1/2)`) the "all connected"
  probabilities differ by `κ = 3/8`.
* The fair coin is invariant under negation.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal
open StatMech StatMech.Universality

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.STT

example : kappaTri (1 / 2) (1 / 2) (1 / 2) = 3 / 8 := by norm_num [kappaTri]

example : IsCriticalSquare (1 / 2) (1 / 2) := by
  rw [isCriticalSquare_iff]; norm_num

theorem crit : IsCriticalTri (1 / 2) (1 / 2) 0 := by
  rw [isCriticalTri_iff]; norm_num

example : triProb (1 / 2) (1 / 2) 0 triPatABC = starProb (1 - 1 / 2) (1 - 1 / 2) (1 - 0) starPatABC ∧
    triProb (1 / 2) (1 / 2) 0 triPatSep = starProb (1 - 1 / 2) (1 - 1 / 2) (1 - 0) starPatSep ∧
    triProb (1 / 2) (1 / 2) 0 triPatAB = starProb (1 - 1 / 2) (1 - 1 / 2) (1 - 0) starPatAB ∧
    triProb (1 / 2) (1 / 2) 0 triPatAC = starProb (1 - 1 / 2) (1 - 1 / 2) (1 - 0) starPatAC ∧
    triProb (1 / 2) (1 / 2) 0 triPatBC = starProb (1 - 1 / 2) (1 - 1 / 2) (1 - 0) starPatBC :=
  starTriangle_connectivity _ _ _ crit

example : triProb (1 / 2) (1 / 2) (1 / 2) triPatABC
    - starProb (1 - 1 / 2) (1 - 1 / 2) (1 - 1 / 2) starPatABC = 3 / 8 := by
  rw [stt_ABC_sub]; norm_num [kappaTri]

example : ¬ IsCriticalTri (1 / 2) (1 / 2) (1 / 2) := by
  rw [isCriticalTri_iff]; norm_num

example : Measure.map (fun b => !b) (bernoulliMeasure 2⁻¹ half_le_one)
    = bernoulliMeasure 2⁻¹ half_le_one := bernoulli_selfDual_half

end MathlibExtTest.StatMech.Probability.Percolation.Universality.STT
