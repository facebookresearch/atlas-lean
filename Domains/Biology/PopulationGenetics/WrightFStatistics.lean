/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic

/-!
# Wright's hierarchical F-statistics

The three indices compare non-identity within an individual, within a subpopulation, and
in the total population. Their complement identity is algebraic: the two successive ratios
multiply to the ratio between the individual and total levels.
-/

namespace Domains.Biology.PopulationGenetics.WrightFStatistics

/-- Wright's hierarchical identity `1 - F_IT = (1 - F_IS) * (1 - F_ST)`, with each index
`F_XY` written as `1 - H_X / H_Y`. Both denominator hypotheses keep the ordinary ratios
well-defined. Only `H_S ≠ 0` is needed for the algebraic equality under Lean's total division.

See Felsenstein, *Theoretical Evolutionary Genetics*, December 2019, §VI.9,
equations (VI-58), (VI-59), and (VI-61). -/
public theorem hierarchical_identity (hI hS hT : ℝ) (hS_ne_zero : hS ≠ 0) (_hT_ne_zero : hT ≠ 0) :
    1 - (1 - hI / hT) = (1 - (1 - hI / hS)) * (1 - (1 - hS / hT)) := by
  simpa only [sub_sub_cancel] using
    (div_mul_div_cancel₀ (a := hI) (c := hT) hS_ne_zero).symm

end Domains.Biology.PopulationGenetics.WrightFStatistics
