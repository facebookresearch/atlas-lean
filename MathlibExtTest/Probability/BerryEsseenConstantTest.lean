/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.BerryEsseenConstant

@[expose] public section

open MeasureTheory ProbabilityTheory BerryEsseenModel BerryEsseenConstant
open scoped ENNReal NNReal

namespace MathlibExtTest.BerryEsseenConstant

example : IsAdmissible 42 := isAdmissible_fortyTwo

example : 0 ≤ value := value_nonnegative

example : value ≤ 42 := value_le_fortyTwo

example : IsLeast {C : ℝ | IsAdmissible C} value := value_isLeast

example : IsAdmissible value := value_isAdmissible

example (C : ℝ) : IsAdmissible C ↔ value ≤ C := isAdmissible_iff_value_le C

example : IsBernoulliLaw symmetricBernoulliLaw := symmetricBernoulli_isBernoulli

example : thirdMoment symmetricBernoulliLaw = 1 := symmetricBernoulli_thirdMoment

example : 0 ≤ bernoulliValue := bernoulliValue_nonnegative

example : bernoulliValue ≤ value := bernoulliValue_le_value

universe u

example {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ}
    (h : IsIIDModel P X) (n : ℕ+) (x : ℝ) :
    |cdf (P.map (fun ω ↦ (∑ i ∈ Finset.range n.1, X i ω) /
        Real.sqrt (n.1 : ℝ))) x - normalCDF x| ≤
      value * (∫ ω, |X 0 ω| ^ 3 ∂P) / Real.sqrt (n.1 : ℝ) :=
  iid_bound value_isAdmissible h n x

end MathlibExtTest.BerryEsseenConstant

#eval "C19 least common coefficient, Bernoulli witness and universe-polymorphic bound elaborated"
