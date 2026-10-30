/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BrownianMotion.BrownianKolmogorovTail
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.BrownianMotion.BrownianKolmogorovTail`

* `brownianCoordinateProcess_measure_edist_ge_le` at `s = 0`, `t = 1`, `δ = 1`:
  `P(|B_0 - B_1| ≥ 1) ≤ 3`.
-/

@[expose] public section

open StatMech.SLE MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MathlibExtTest.StatMech.Probability.BrownianMotion.BrownianKolmogorovTail

example : brownianProductLaw {ω | (1 : ℝ≥0∞) ≤
    edist (brownianCoordinateProcess 0 ω) (brownianCoordinateProcess 1 ω)} ≤
      ((3 : ℝ≥0) * edist (0 : ℝ) 1 ^ (2 : ℝ)) / 1 ^ (4 : ℕ) :=
  brownianCoordinateProcess_measure_edist_ge_le 0 1 1 one_ne_zero ENNReal.one_ne_top

end MathlibExtTest.StatMech.Probability.BrownianMotion.BrownianKolmogorovTail
