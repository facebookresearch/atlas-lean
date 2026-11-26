/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DigitSumDirichletConvolutionDigitSumAuxiliaryIsBigO
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.NumberTheory.DigitSumDirichletConvolutionDigitSumAuxiliaryIsBigO` -/

namespace MathlibExtTest.NumberTheory.DigitSumDirichletConvolutionDigitSumAuxiliaryIsBigO

open MetaMathlibExt Filter Asymptotics Real

-- Delange's series in base two is bounded at infinity.
example : trollopeDelangeSeries 2 =O[atTop] (fun _ => (1 : ℝ)) :=
  (digitSum_auxiliary_isBigO 2 le_rfl).1

-- The base-ten fluctuation is uniformly bounded.
example : ∃ C : ℝ, ∀ x : ℝ, |trollopeDelangeFluctuation 10 x| ≤ C :=
  (digitSum_auxiliary_isBigO 10 (by norm_num)).2.1

-- Hence the base-three fluctuation at any fixed point has a uniform bound.
example (x : ℝ) : ∃ C : ℝ, |trollopeDelangeFluctuation 3 x| ≤ C :=
  let ⟨C, hC⟩ := (digitSum_auxiliary_isBigO 3 (by norm_num)).2.1
  ⟨C, hC x⟩

-- The base-seven remainder is `O(log x)`.
example : digitSumRemainder 7 =O[atTop] log :=
  (digitSum_auxiliary_isBigO 7 (by norm_num)).2.2.1

-- The base-four fluctuation integral `G` is `O(log x)`.
example : digitSumFluctuationIntegral 4 =O[atTop] log :=
  (digitSum_auxiliary_isBigO 4 (by norm_num)).2.2.2.1

-- The base-two double fluctuation integral is `O(log x ^ 2)`.
example : digitSumFluctuationDoubleIntegral 2 =O[atTop] (fun x => log x ^ 2) :=
  (digitSum_auxiliary_isBigO 2 le_rfl).2.2.2.2.1

-- The base-six remainder integral `K` is bounded at infinity.
example : digitSumRemainderIntegral 6 =O[atTop] (fun _ => (1 : ℝ)) :=
  (digitSum_auxiliary_isBigO 6 (by norm_num)).2.2.2.2.2.1

-- The base-five double remainder integral is `O(log x)`.
example : digitSumRemainderDoubleIntegral 5 =O[atTop] log :=
  (digitSum_auxiliary_isBigO 5 (by norm_num)).2.2.2.2.2.2

end MathlibExtTest.NumberTheory.DigitSumDirichletConvolutionDigitSumAuxiliaryIsBigO
