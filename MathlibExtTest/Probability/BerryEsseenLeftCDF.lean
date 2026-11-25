/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.BerryEsseenConstant
import MathlibExt.Probability.BerryEsseenLeftCDF

open MeasureTheory ProbabilityTheory BerryEsseenModel BerryEsseenConstant

-- A standardized atomic law: the strict and non-strict CDFs differ at its atoms.
example : sSup (Set.range (fun x : ℝ ↦
    |symmetricBernoulliLaw.real (Set.Iio x) - normalCDF x|)) =
      kolmogorovError symmetricBernoulliLaw ⟨1, by decide⟩ := by
  have h := BerryEsseenWanted.leftRightCDFErrorEquivalence_holds
    symmetricBernoulliLaw symmetricBernoulli_isStandardized ⟨1, by decide⟩
  simpa only [normalizedLaw_one symmetricBernoulli_isStandardized] using h
