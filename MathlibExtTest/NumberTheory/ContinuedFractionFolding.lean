/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ContinuedFractionFolding
import Mathlib.Tactic.NormNum

/-!
# Tests for digit frequencies in Cloitre's approximants

The difference between the proportions of digits `1` and `2` tends to `1/3`.

Source: Daniel J. Hoyt, *The Self-Describing Paperfolding Sequence in Continued Fractions*,
Journal of Integer Sequences 29 (2026), Article 26.3.6, Theorem 17.
-/

namespace MathlibExtTest.NumberTheory.ContinuedFractionFolding

open MetaMathlibExt

example :
    Filter.Tendsto (fun k =>
      ((cloitreApprox k).count 1 : ℝ) / (cloitreApprox k).length -
        ((cloitreApprox k).count 2 : ℝ) / (cloitreApprox k).length)
      Filter.atTop (nhds (1 / 3)) := by
  obtain ⟨h₁, h₂⟩ := tendsto_cloitreApprox_count_div_length
  convert h₁.sub h₂ using 1
  norm_num

end MathlibExtTest.NumberTheory.ContinuedFractionFolding
