/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.CarlitzBetaClosedForms

namespace MetaMathlibExt

open Finset

-- Order zero uses the exceptional coefficient at k = 0, including when q is below one.
example (x : ℝ) : extendedCarlitzBetaPoly (1 / 2) 0 0 x = 1 := by
  simpa using (extendedCarlitzBetaPoly_closed_forms (1 / 2) (by norm_num) (by norm_num) 0).1 0 x

-- The degree-one binomial expansion at order zero reduces to the bracket at every real argument.
example (x : ℝ) : extendedCarlitzBetaPoly 2 0 1 x = qBracket 2 x := by
  have hq : (2 : ℝ) ≠ 1 := by norm_num
  have h := (extendedCarlitzBetaPoly_closed_forms 2 (by norm_num) hq 0).2.1 1 x
  simpa [sum_range_succ, extendedCarlitzBetaPoly_zero, carlitzEtaPoly_zero,
    carlitzEtaPoly_one_zero hq] using h

-- At positive order the recurrence determines the value at its first applicable degree.
example : extendedCarlitzBetaPoly 2 1 2 0 = 2 / 21 := by
  have h := extendedCarlitzBetaPoly_closed_forms 2 (by norm_num) (by norm_num) 1
  have h0 := h.1 0 0
  have h1 := h.1 1 0
  have h2 := h.2.2 2 (by decide)
  norm_num [sum_range_succ, qBracket, Real.rpow_natCast] at h0 h1
  norm_num [sum_range_succ] at h2
  linarith

end MetaMathlibExt
