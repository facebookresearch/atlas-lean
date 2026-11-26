/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Configuration.TailSpecification

/-!
# Tests for `MathlibExt.Probability.Configuration.TailSpecification`

* `ts_cond_congr` and `ts_trim_smul` at the Dirac measure on `Bool`.
* Not covered: `ts_isErgodic_of_extreme` needs a family of specification kernels
  `K n` consistent with a translation-invariant measure; building one is beyond the test budget.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open StatMech

namespace MathlibExtTest.StatMech.Probability.Configuration.TailSpecification

example (s t : Set Bool) (h : s =ᵐ[(Measure.dirac true : Measure Bool)] t) :
    (Measure.dirac true : Measure Bool)[|s]
      = (Measure.dirac true : Measure Bool)[|t] :=
  ts_cond_congr _ h

example : ((2 : ℝ≥0∞) • (Measure.dirac true : Measure Bool)).trim le_rfl
    = (2 : ℝ≥0∞) • (Measure.dirac true : Measure Bool).trim le_rfl :=
  ts_trim_smul _ le_rfl 2

end MathlibExtTest.StatMech.Probability.Configuration.TailSpecification
