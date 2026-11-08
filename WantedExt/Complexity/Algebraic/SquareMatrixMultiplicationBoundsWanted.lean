/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Complexity.Algebraic.RectangularCircuitExponent
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Square matrix-multiplication exponent: source-bound requests

All `theorem_wanted` declarations below are private unproved `ProofWanted` data.
The optimizer is the aspect-one case of the actual arithmetic-circuit exponent:
the inner dimension is exactly `n`, each addition, subtraction or multiplication
node costs one, and constants, input references and output references are free.
The output-cost lower bound `2 ≤ ω` is proved upstream as
`two_le_squareMatrixMultiplicationCircuitExponent`.

The catalogue rows are stated for every field. Transfers from approximate or
border-rank algorithms, recursive tensor constructions, division elimination,
the operation/rank bridge and characteristic invariance are not proved here.
The final sharpness proposition records the catalogue comment that `2` is
conjectured sharp; it is a definition, not an asserted theorem.
-/

set_option autoImplicit false

namespace Cslib.Complexity.Algebraic.SquareMatrixMultiplicationBoundsWanted

open Cslib.Complexity.Algebraic

universe u v

/-- The catalogue comment that the trivial lower bound two is conjectured sharp.
This proposition is not asserted. -/
def omegaEqualsTwoConjecture : Prop :=
  ∀ (F : Type u) [Field F], squareMatrixMultiplicationCircuitExponent F = 2

/-- Source: C15a, trivial upper bound. The general finite naive circuit
construction is not supplied upstream, so this remains a proof request. -/
theorem_wanted naiveUpperThree :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤ ENNReal.ofReal 3

/-- Source: C15a [S1969], Strassen's `log₂ 7` bound. -/
theorem_wanted strassen1969Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal (Real.log 7 / Real.log 2)

/-- Source: C15a [P1978], Pan's `log₇₀ 143640` bound. -/
theorem_wanted pan1978Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal (Real.log 143640 / Real.log 70)

/-- Source: C15a [BCRL1979, B1980], the `3 log₁₂ 10` approximate-algorithm bound. -/
theorem_wanted biniCapovaniRomaniLotti1979Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal (3 * (Real.log 10 / Real.log 12))

/-- Source: C15a [P1979], Pan's `3 log₄₃₆ 196` bound. -/
theorem_wanted pan1979Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal (3 * (Real.log 196 / Real.log 436))

/-- Source: C15a [P1980], Pan's `log₄₈ 47216` bound. -/
theorem_wanted pan1980Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal (Real.log 47216 / Real.log 48)

/-- Source: C15a [S1981], Schönhage's `log₁₁₀ 140600` bound. -/
theorem_wanted schonhage1981Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal (Real.log 140600 / Real.log 110)

/-- Source: C15a [P1981], Pan's decimal bound `2.5161`. -/
theorem_wanted pan1981Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((25161 : ℝ) / 10000)

/-- Source: C15a [R1982], Romani's decimal bound `2.5166`. -/
theorem_wanted romani1982Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((25166 : ℝ) / 10000)

/-- Source: C15a [CW1982], Coppersmith--Winograd bound `2.495548`. -/
theorem_wanted coppersmithWinograd1982Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((2495548 : ℝ) / 1000000)

/-- Source: C15a [S1987], Strassen's laser-method bound `2.4785`. -/
theorem_wanted strassen1987Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((24785 : ℝ) / 10000)

/-- Source: C15a [CW1990], Coppersmith--Winograd bound `2.375477`. -/
theorem_wanted coppersmithWinograd1990Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((2375477 : ℝ) / 1000000)

/-- Source: C15a [CKSU2005], group-theoretic bound `2.41`. -/
theorem_wanted cohnKleinbergSzegedyUmans2005Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((241 : ℝ) / 100)

/-- Source: C15a [S2010, DS2013], bound `2.373689703`. -/
theorem_wanted stothersDavie2013Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((2373689703 : ℝ) / 1000000000)

/-- Source: C15a [V2012, V2014], Vassilevska Williams bound `2.372873`. -/
theorem_wanted vassilevskaWilliams2012Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((2372873 : ℝ) / 1000000)

/-- Source: C15a [Z2012], Zhdanovich bound `2.373`. -/
theorem_wanted zhdanovich2012Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((2373 : ℝ) / 1000)

/-- Source: C15a [LG2014], Le Gall bound `2.3728639`. -/
theorem_wanted leGall2014Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((23728639 : ℝ) / 10000000)

/-- Source: C15a [AV2020], Alman--Vassilevska Williams bound `2.3728596`. -/
theorem_wanted almanVassilevskaWilliams2020Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((23728596 : ℝ) / 10000000)

/-- Source: C15a [DWZ2022], Duan--Wu--Zhou bound `2.371866`. -/
theorem_wanted duanWuZhou2022Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((2371866 : ℝ) / 1000000)

/-- Source: C15a [VXXZ2023], bound `2.371552`. -/
theorem_wanted vassilevskaWilliamsXuXuZhou2023Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((2371552 : ℝ) / 1000000)

/-- Source: C15a [ADVXXZ2024], bound `2.371339`. -/
theorem_wanted almanDuanVassilevskaWilliamsXuXuZhou2024Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((2371339 : ℝ) / 1000000)

/-- Source: C15a [DEKMRSZAWB2026], best catalogue bound `2.371177`. -/
theorem_wanted dupontEisenbergerEtAl2026Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((2371177 : ℝ) / 1000000)

/-- Source: C15a additional comments and [B2013]: the arithmetic-operation
exponent agrees with the tensor-rank exponent. This bridge is not proved. -/
theorem_wanted squareOperationRankBridge :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F =
        MatrixMultiplicationExponent.matrixMultiplicationExponent F

/-- Source: C15a additional comments and [S1981]: the exponent depends only on
the field characteristic. This circuit-model transfer is not proved. -/
theorem_wanted characteristicInvariance :
    ∀ (F : Type u) (K : Type v) [Field F] [Field K], ringChar F = ringChar K →
      squareMatrixMultiplicationCircuitExponent F =
        squareMatrixMultiplicationCircuitExponent K

end Cslib.Complexity.Algebraic.SquareMatrixMultiplicationBoundsWanted
