/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecificLimits.DiscountedTruncationCertificate
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.Analysis.SpecificLimits.DiscountedTruncationCertificate

open MathlibExt.DiscountedSum

/-- The `T = 5`, `β = 1/2` truncation itself equals `31/16`. -/
example : truncatedValue (1 / 2) (fun _ => 1) 5 = 31 / 16 := by
  norm_num [truncatedValue, Finset.sum_range_succ]

end MathlibExtTest.Analysis.SpecificLimits.DiscountedTruncationCertificate
