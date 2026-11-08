/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.AlgebraicGeometry.SeshadriConstant

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.SeshadriConstantWanted

open MathlibExt.AlgebraicGeometry.SeshadriConstant

/-!
# Catalogue bounds for the ten-point Seshadri constant

The frozen catalogue bounds for `C₇₄` as proof requests against
`seshadriConstant10`. The Lean constant is the supremum over injective
affine ten-point configurations of the infimum of degree over summed
multiplicities. Harbourne--Roé define the generic constant by this
supremum and identify it with the value at very general points; the
projective chart identification is not formalized here.
-/

/-- The Nagata prediction for ten points, recorded as a proposition only.
It is not asserted. -/
def nagataConjecture10 : Prop :=
  seshadriConstant10 = 1 / Real.sqrt 10

/-- Source: Eckl (2008), asymptotic Dumnicki method, catalogue lower bound `4/13`. -/
theorem_wanted eckl2008LowerBound_wanted :
    (4 / 13 : ℝ) ≤ seshadriConstant10

/-- Source: Harbourne--Roé (2009), nef divisor bound `177/560`. -/
theorem_wanted harbourneRoe2009LowerBound_wanted :
    (177 / 560 : ℝ) ≤ seshadriConstant10

/-- Source: Ciliberto--Miranda (2011), degeneration bound `55/174`. -/
theorem_wanted cilibertoMiranda2011LowerBound_wanted :
    (55 / 174 : ℝ) ≤ seshadriConstant10

/-- Source: Eckl (2011), improved catalogue lower bound `117/370`. -/
theorem_wanted eckl2011LowerBound_wanted :
    (117 / 370 : ℝ) ≤ seshadriConstant10

/-- Source: the general submaximal upper bound `ε ≤ √(D²/r)` for
`D = 𝒪_{ℙ²}(1)` and `r = 10`. -/
theorem_wanted submaximalUpperBound_wanted :
    seshadriConstant10 ≤ 1 / Real.sqrt 10

end MathlibExt.AlgebraicGeometry.SeshadriConstantWanted
