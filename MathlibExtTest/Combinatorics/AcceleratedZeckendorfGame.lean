/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.AcceleratedZeckendorfGame

/-! # Tests for the Accelerated Zeckendorf Game -/

namespace MetaMathlibExt.accelZeckMove_fib_combine

open Finsupp

-- At the smallest indices, one pair combines and both input piles are exhausted.
example : AccelZeckMove (single 2 1 + single 1 1) (single 3 1) := by
  have h := (accelZeckMove_fib_combine 2 1 (by decide) (by decide)
    (single 2 1 + single 1 1) (by simp) (by simp) (by simp)).1
  change AccelZeckMove _ ((single 2 1 + single 1 1) - single 1 1 - single 2 1 + single 3 1) at h
  simpa using h

-- Two pairs combine at once, leaving one copy at the middle index.
example : AccelZeckMove (single 2 3 + single 1 2) (single 2 1 + single 3 2) := by
  have h := (accelZeckMove_fib_combine 2 3 (by decide) (by decide)
    (single 2 3 + single 1 2) (by simp [Nat.fib_add_two])
    (by simp [Nat.fib_add_two]) (by simp)).1
  change AccelZeckMove _ ((single 2 3 + single 1 2 - single 1 2) - single 2 2 + single 3 2) at h
  simpa [← single_tsub] using h

end MetaMathlibExt.accelZeckMove_fib_combine

namespace MetaMathlibExt

-- Apply the implication at the first starting size covered by Conjecture 1.6.
example (h17 : ∀ n, AccelZeckLosing (Finsupp.single 1 n) → ∀ k, 3 * k ≤ n →
    AccelZeckLosing (Finsupp.single 3 k + Finsupp.single 1 (n - 3 * k))) :
    AccelZeckWinning (Finsupp.single 1 10) :=
  accelZeck_conjecture17_implies_conjecture16 (h17 := h17) 10 (by decide)

end MetaMathlibExt
