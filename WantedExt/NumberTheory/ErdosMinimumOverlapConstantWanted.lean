/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.NumberTheory.ErdosMinimumOverlapConstant

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

/-!
Source: Optimization Problems, Constant 1b, frozen at commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`, `constants/1b.md`, SHA-256
`1c51678108c90a2e841e1b49fa97940e4e1870324e1d949ddcb5b4345a0153ec`.
The source gives an optimization problem with known bounds and a known discrete
equivalence, but no supported exact-value conjecture. The half upper bound is
proved in the upstream model; the seventeen other claims are explicit
`theorem_wanted` declarations.
The decimal payloads are literal source requests, not certified rounded bounds.
Full primary-paper and numerical-certificate verification remains deferred.
-/

/-- The source-reported equivalence between the continuous constant and Erdős Problem 36.
Source: Haugland 2016; Optimization Problems, Constant 1b. -/
def continuousDiscreteEquivalence : Prop :=
  Filter.Tendsto MinOverlapQuotient Filter.atTop (nhds C₁ᵦ)

/-- The source's uniform `o(1)` partition statement and largest-constant assertion.
Source: Haugland 2016; Optimization Problems, Constant 1b. -/
def continuousDiscreteAsymptoticCharacterization : Prop :=
  IsGreatest {c : ℝ | DiscreteUniversalLowerBound c} C₁ᵦ

/-- Source-reported upper bound `C₁ᵦ ≤ 1/2`.
Source: Erdős 1955; Optimization Problems, Constant 1b. -/
def upperBound_E1955_half : Prop := C₁ᵦ ≤ (1 : ℝ) / 2

/-- Source-reported unpublished upper bound `C₁ᵦ ≤ 4/9`.
Source: Erdős, unpublished; Optimization Problems, Constant 1b. -/
def upperBound_Erdos_unpublished_fourNinths : Prop := C₁ᵦ ≤ (4 : ℝ) / 9

/-- Source-reported upper bound `C₁ᵦ ≤ 5/12`.
Source: Motzkin--Ralston--Selfridge 1956; Optimization Problems, Constant 1b. -/
def upperBound_MRS1956_fiveTwelfths : Prop := C₁ᵦ ≤ (5 : ℝ) / 12

/-- Source-reported exact terminating-decimal upper bound `C₁ᵦ ≤ 0.4`.
Source: Motzkin--Ralston--Selfridge 1956; Optimization Problems, Constant 1b. -/
def upperBound_MRS1956_pointFour : Prop := C₁ᵦ ≤ (4 : ℝ) / 10

/-- Source-reported unpublished 1993 Haugland upper bound.
Source: Haugland, unpublished 1993; Optimization Problems, Constant 1b. -/
def upperBound_Haugland_unpublished_1993 : Prop := C₁ᵦ ≤ (385694 : ℝ) / 1000000

/-- Source-reported Haugland 1996 upper bound.
Source: Haugland 1996; Optimization Problems, Constant 1b. -/
def upperBound_H1996 : Prop := C₁ᵦ ≤ (382002 : ℝ) / 1000000

/-- Source-reported Haugland 2016 upper bound.
Source: Haugland 2016; Optimization Problems, Constant 1b. -/
def upperBound_H2016 : Prop := C₁ᵦ ≤ (380926 : ℝ) / 1000000

/-- Source-reported AlphaEvolve 2025 upper bound.
Source: Georgiev--Gómez-Serrano--Tao--Wagner 2025; Optimization Problems, Constant 1b. -/
def upperBound_GGSWT2025_AlphaEvolve : Prop := C₁ᵦ ≤ (380924 : ℝ) / 1000000

/-- Source-reported TTT-Discover 2026 upper bound.
Source: Yuksekgonul et al. 2026 (TTT-Discover); Optimization Problems, Constant 1b. -/
def upperBound_YKLBMWKCZGS2026_TTTDiscover : Prop := C₁ᵦ ≤ (380876 : ℝ) / 1000000

/-- Source-reported Together AI 2026 upper bound.
Source: Together AI 2026; Optimization Problems, Constant 1b. -/
def upperBound_T2026_TogetherAI : Prop := C₁ᵦ ≤ (380871 : ℝ) / 1000000

/-- Source-reported SimpleTES 2026 upper bound.
Source: Ye et al. 2026 (SimpleTES); Optimization Problems, Constant 1b. -/
def upperBound_YLTLYSTYLLGDHZSWZSHMELCZX2026_SimpleTES : Prop :=
  C₁ᵦ ≤ (380868 : ℝ) / 1000000

/-- Source-reported lower bound `1/4 ≤ C₁ᵦ`.
Source: Erdős 1955; Optimization Problems, Constant 1b. -/
def lowerBound_E1955_quarter : Prop := (1 : ℝ) / 4 ≤ C₁ᵦ

/-- Source-reported unpublished Scherk lower bound `1 - 1/√2 ≤ C₁ᵦ`.
Source: Scherk, unpublished 1955; Optimization Problems, Constant 1b. -/
def lowerBound_Scherk_unpublished_1955 : Prop := 1 - 1 / Real.sqrt 2 ≤ C₁ᵦ

/-- Source-reported lower bound `(4-√6)/5 ≤ C₁ᵦ`.
Source: Swierczkowski 1958; Optimization Problems, Constant 1b. -/
def lowerBound_S1958 : Prop := (4 - Real.sqrt 6) / 5 ≤ C₁ᵦ

/-- Source-reported lower bound `√(4-√15) ≤ C₁ᵦ`.
Source: Moser 1959; Optimization Problems, Constant 1b. -/
def lowerBound_M1959 : Prop := Real.sqrt (4 - Real.sqrt 15) ≤ C₁ᵦ

/-- Source-reported exact terminating-decimal lower bound `0.379005 ≤ C₁ᵦ`.
Source: White 2022; Optimization Problems, Constant 1b. -/
def lowerBound_W2022 : Prop := (379005 : ℝ) / 1000000 ≤ C₁ᵦ

/-- Source: Haugland 2016 and Optimization Problems 1b. -/
public theorem_wanted continuousDiscreteEquivalence_holds : continuousDiscreteEquivalence

/-- Source: Haugland 2016 and the uniform partition clause of Optimization Problems 1b. -/
public theorem_wanted continuousDiscreteAsymptoticCharacterization_holds :
  continuousDiscreteAsymptoticCharacterization

/-- Source: Erdős, unpublished, recorded by Optimization Problems 1b. -/
public theorem_wanted upperBound_Erdos_unpublished_fourNinths_holds :
  upperBound_Erdos_unpublished_fourNinths

/-- Source: Motzkin--Ralston--Selfridge 1956 and Optimization Problems 1b. -/
public theorem_wanted upperBound_MRS1956_fiveTwelfths_holds : upperBound_MRS1956_fiveTwelfths

/-- Source: Motzkin--Ralston--Selfridge 1956 and Optimization Problems 1b. -/
public theorem_wanted upperBound_MRS1956_pointFour_holds : upperBound_MRS1956_pointFour

/-- Source: Haugland, unpublished 1993, recorded by Optimization Problems 1b. -/
public theorem_wanted upperBound_Haugland_unpublished_1993_holds :
  upperBound_Haugland_unpublished_1993

/-- Source: Haugland 1996 and Optimization Problems 1b. -/
public theorem_wanted upperBound_H1996_holds : upperBound_H1996

/-- Source: Haugland 2016 and Optimization Problems 1b. -/
public theorem_wanted upperBound_H2016_holds : upperBound_H2016

/-- Source: Georgiev--Gómez-Serrano--Tao--Wagner 2025 and Optimization Problems 1b. -/
public theorem_wanted upperBound_GGSWT2025_AlphaEvolve_holds :
  upperBound_GGSWT2025_AlphaEvolve

/-- Source: Yuksekgonul et al. 2026 and Optimization Problems 1b. -/
public theorem_wanted upperBound_YKLBMWKCZGS2026_TTTDiscover_holds :
  upperBound_YKLBMWKCZGS2026_TTTDiscover

/-- Source: Together AI 2026 and Optimization Problems 1b. -/
public theorem_wanted upperBound_T2026_TogetherAI_holds : upperBound_T2026_TogetherAI

/-- Source: Ye et al. 2026 and Optimization Problems 1b. -/
public theorem_wanted upperBound_YLTLYSTYLLGDHZSWZSHMELCZX2026_SimpleTES_holds :
  upperBound_YLTLYSTYLLGDHZSWZSHMELCZX2026_SimpleTES

/-- Source: Erdős 1955 and Optimization Problems 1b. -/
public theorem_wanted lowerBound_E1955_quarter_holds : lowerBound_E1955_quarter

/-- Source: Scherk, unpublished 1955, recorded by Optimization Problems 1b. -/
public theorem_wanted lowerBound_Scherk_unpublished_1955_holds :
  lowerBound_Scherk_unpublished_1955

/-- Source: Swierczkowski 1958 and Optimization Problems 1b. -/
public theorem_wanted lowerBound_S1958_holds : lowerBound_S1958

/-- Source: Moser 1959 and Optimization Problems 1b. -/
public theorem_wanted lowerBound_M1959_holds : lowerBound_M1959

/-- Source: White 2022 and Optimization Problems 1b. -/
public theorem_wanted lowerBound_W2022_holds : lowerBound_W2022

end MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted
