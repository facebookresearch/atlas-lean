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

/-- **Conjecture that the square exponent is two.** The proposition that for every field $F$,
the square matrix multiplication exponent $\omega(F)$ of the arithmetic-circuit model equals $2$.

Since $\omega(F) \ge 2$ always holds, this says the trivial lower bound is sharp. It is a
conjecture, recorded as a proposition and not asserted. -/
def omegaEqualsTwoConjecture : Prop :=
  ∀ (F : Type u) [Field F], squareMatrixMultiplicationCircuitExponent F = 2

/-- **Naive bound for square matrix multiplication.** For every field $F$, the square matrix
multiplication exponent $\omega(F)$ of the arithmetic-circuit model satisfies $\omega(F) \le 3$.

Source: C15a, trivial upper bound. The general finite naive circuit
construction is not supplied upstream, so this remains a proof request. -/
theorem_wanted naiveUpperThree :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤ ENNReal.ofReal 3

/-- **Strassen's 1969 bound on the matrix multiplication exponent.** For every field $F$, the
square matrix multiplication exponent $\omega(F)$ of the arithmetic-circuit model satisfies
$\omega(F) \le \log_2 7$.

Source: C15a [S1969], Strassen's `log₂ 7` bound. -/
theorem_wanted strassen1969Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal (Real.log 7 / Real.log 2)

/-- **Pan's 1978 bound on the square exponent.** For every field $F$, the square matrix
multiplication exponent $\omega(F)$ of the arithmetic-circuit model satisfies
$\omega(F) \le \log_{70} 143640$.

Source: C15a [P1978], Pan's `log₇₀ 143640` bound. -/
theorem_wanted pan1978Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal (Real.log 143640 / Real.log 70)

/-- **Bini–Capovani–Romani–Lotti bound on the square exponent.** For every field $F$, the square
matrix multiplication exponent $\omega(F)$ of the arithmetic-circuit model satisfies
$\omega(F) \le 3 \log_{12} 10$.

Source: C15a [BCRL1979, B1980], the `3 log₁₂ 10` approximate-algorithm bound. -/
theorem_wanted biniCapovaniRomaniLotti1979Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal (3 * (Real.log 10 / Real.log 12))

/-- **Pan's 1979 bound on the matrix multiplication exponent.** For every field $F$, the square
matrix multiplication exponent $\omega(F)$ of the arithmetic-circuit model satisfies
$\omega(F) \le 3 \log_{436} 196$.

Source: C15a [P1979], Pan's `3 log₄₃₆ 196` bound. -/
theorem_wanted pan1979Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal (3 * (Real.log 196 / Real.log 436))

/-- **Pan's 1980 bound on the matrix multiplication exponent.** For every field $F$, the square
matrix multiplication exponent $\omega(F)$ of the arithmetic-circuit model satisfies
$\omega(F) \le \log_{48} 47216$.

Source: C15a [P1980], Pan's `log₄₈ 47216` bound. -/
theorem_wanted pan1980Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal (Real.log 47216 / Real.log 48)

/-- **Schönhage's 1981 bound on the matrix multiplication exponent.** For every field $F$, the
square matrix multiplication exponent $\omega(F)$ of the arithmetic-circuit model satisfies
$\omega(F) \le \log_{110} 140600$.

Source: C15a [S1981], Schönhage's `log₁₁₀ 140600` bound. -/
theorem_wanted schonhage1981Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal (Real.log 140600 / Real.log 110)

/-- **Pan's 1981 bound on the matrix multiplication exponent.** For every field $F$, the square
matrix multiplication exponent $\omega(F)$ of the arithmetic-circuit model satisfies
$\omega(F) \le 2.5161$.

Source: C15a [P1981], Pan's decimal bound `2.5161`. -/
theorem_wanted pan1981Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((25161 : ℝ) / 10000)

/-- **Romani's 1982 bound on the matrix multiplication exponent.** For every field $F$, the
square matrix multiplication exponent $\omega(F)$ of the arithmetic-circuit model satisfies
$\omega(F) \le 2.5166$.

Source: C15a [R1982], Romani's decimal bound `2.5166`. -/
theorem_wanted romani1982Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((25166 : ℝ) / 10000)

/-- **Coppersmith–Winograd 1982 bound on the square exponent.** For every field $F$, the square
matrix multiplication exponent $\omega(F)$ of the arithmetic-circuit model satisfies
$\omega(F) \le 2.495548$.

Source: C15a [CW1982], Coppersmith--Winograd bound `2.495548`. -/
theorem_wanted coppersmithWinograd1982Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((2495548 : ℝ) / 1000000)

/-- **Strassen's 1987 bound on the matrix multiplication exponent.** For every field $F$, the
square matrix multiplication exponent $\omega(F)$ of the arithmetic-circuit model satisfies
$\omega(F) \le 2.4785$.

Source: C15a [S1987], Strassen's laser-method bound `2.4785`. -/
theorem_wanted strassen1987Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((24785 : ℝ) / 10000)

/-- **Coppersmith–Winograd 1990 bound on the square exponent.** For every field $F$, the square
matrix multiplication exponent $\omega(F)$ of the arithmetic-circuit model satisfies
$\omega(F) \le 2.375477$.

Source: C15a [CW1990], Coppersmith--Winograd bound `2.375477`. -/
theorem_wanted coppersmithWinograd1990Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((2375477 : ℝ) / 1000000)

/-- **Cohn–Kleinberg–Szegedy–Umans bound on the square exponent.** For every field $F$, the
square matrix multiplication exponent $\omega(F)$ of the arithmetic-circuit model satisfies
$\omega(F) \le 2.41$.

Source: C15a [CKSU2005], group-theoretic bound `2.41`. -/
theorem_wanted cohnKleinbergSzegedyUmans2005Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((241 : ℝ) / 100)

/-- **Stothers–Davie bound on the matrix multiplication exponent.** For every field $F$, the
square matrix multiplication exponent $\omega(F)$ of the arithmetic-circuit model satisfies
$\omega(F) \le 2.373689703$.

Source: C15a [S2010, DS2013], bound `2.373689703`. -/
theorem_wanted stothersDavie2013Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((2373689703 : ℝ) / 1000000000)

/-- **Vassilevska Williams's 2012 bound on the matrix multiplication exponent.** For every
field $F$, the square matrix multiplication exponent $\omega(F)$ of the arithmetic-circuit model
satisfies $\omega(F) \le 2.372873$.

Source: C15a [V2012, V2014], Vassilevska Williams bound `2.372873`. -/
theorem_wanted vassilevskaWilliams2012Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((2372873 : ℝ) / 1000000)

/-- **Zhdanovich's 2012 bound on the matrix multiplication exponent.** For every field $F$, the
square matrix multiplication exponent $\omega(F)$ of the arithmetic-circuit model satisfies
$\omega(F) \le 2.373$.

Source: C15a [Z2012], Zhdanovich bound `2.373`. -/
theorem_wanted zhdanovich2012Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((2373 : ℝ) / 1000)

/-- **Le Gall's 2014 bound on the square exponent.** For every field $F$, the square matrix
multiplication exponent $\omega(F)$ of the arithmetic-circuit model satisfies
$\omega(F) \le 2.3728639$.

Source: C15a [LG2014], Le Gall bound `2.3728639`. -/
theorem_wanted leGall2014Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((23728639 : ℝ) / 10000000)

/-- **Alman–Vassilevska Williams 2020 bound on the square exponent.** For every field $F$, the
square matrix multiplication exponent $\omega(F)$ of the arithmetic-circuit model satisfies
$\omega(F) \le 2.3728596$.

Source: C15a [AV2020], Alman--Vassilevska Williams bound `2.3728596`. -/
theorem_wanted almanVassilevskaWilliams2020Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((23728596 : ℝ) / 10000000)

/-- **Duan–Wu–Zhou bound on the square exponent.** For every field $F$, the square matrix
multiplication exponent $\omega(F)$ of the arithmetic-circuit model satisfies
$\omega(F) \le 2.371866$.

Source: C15a [DWZ2022], Duan--Wu--Zhou bound `2.371866`. -/
theorem_wanted duanWuZhou2022Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((2371866 : ℝ) / 1000000)

/-- **Vassilevska Williams–Xu–Xu–Zhou upper bound for matrix multiplication.** For every field
$F$, the square matrix multiplication exponent of $F$ in the arithmetic-circuit model is at
most $2.371552$.

Source: C15a [VXXZ2023], bound `2.371552`. -/
theorem_wanted vassilevskaWilliamsXuXuZhou2023Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((2371552 : ℝ) / 1000000)

/-- **Alman–Duan–Vassilevska Williams–Xu–Xu–Zhou upper bound for matrix multiplication.** For
every field $F$, the square matrix multiplication exponent of $F$ in the arithmetic-circuit
model is at most $2.371339$.

Source: C15a [ADVXXZ2024], bound `2.371339`. -/
theorem_wanted almanDuanVassilevskaWilliamsXuXuZhou2024Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((2371339 : ℝ) / 1000000)

/-- **Dupont–Eisenberger et al. upper bound for matrix multiplication.** For every field $F$,
the square matrix multiplication exponent of $F$ in the arithmetic-circuit model is at most
$2.371177$.

Source: C15a [DEKMRSZAWB2026], best catalogue bound `2.371177`. -/
theorem_wanted dupontEisenbergerEtAl2026Upper :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F ≤
        ENNReal.ofReal ((2371177 : ℝ) / 1000000)

/-- **Circuit size and tensor rank give the same square exponent.** For every field $F$, the
square matrix multiplication exponent of $F$ defined by arithmetic-circuit size equals the
matrix multiplication exponent of $F$ defined by tensor rank.

Source: C15a additional comments and [B2013]: the arithmetic-operation
exponent agrees with the tensor-rank exponent. This bridge is not proved. -/
theorem_wanted squareOperationRankBridge :
    ∀ (F : Type u) [Field F],
      squareMatrixMultiplicationCircuitExponent F =
        MatrixMultiplicationExponent.matrixMultiplicationExponent F

/-- **The square exponent depends only on the characteristic.** If two fields $F$ and $K$ have
the same characteristic, then the square matrix multiplication exponents of $F$ and $K$ in the
arithmetic-circuit model are equal.

Source: C15a additional comments and [S1981]: the exponent depends only on
the field characteristic. This circuit-model transfer is not proved. -/
theorem_wanted characteristicInvariance :
    ∀ (F : Type u) (K : Type v) [Field F] [Field K], ringChar F = ringChar K →
      squareMatrixMultiplicationCircuitExponent F =
        squareMatrixMultiplicationCircuitExponent K

end Cslib.Complexity.Algebraic.SquareMatrixMultiplicationBoundsWanted
