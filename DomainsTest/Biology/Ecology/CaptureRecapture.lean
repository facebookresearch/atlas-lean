/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Ecology.CaptureRecapture

open ProbabilityTheory WantedExt.Biology.Ecology.CaptureRecaptureWanted

-- With no marked animals, the count is zero and the estimate is the second sample size.
example : ∑ k ∈ Finset.range (1 + 1), hypergeometricReal 2 0 1 k * chapman 0 1 k = 1 := by
  rw [expectation_chapman (by decide) (by decide)]
  norm_num [Nat.choose]

-- The two possible recapture counts are equally likely and give estimates 3 and 1.
example : ∑ k ∈ Finset.range (1 + 1), hypergeometricReal 2 1 1 k * chapman 1 1 k = 2 := by
  rw [expectation_chapman (by decide) (by decide)]
  norm_num [Nat.choose]
