/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.KeyTheorems.MajorityNotInAC0

open Cslib.Complexity.Classes
open MetaMathlibExt.Complexity.KeyTheorems.MajorityNotInAC0

example : majorityDec ∉ AC0 := majority_not_in_ac0

-- Ties, including the empty string, are rejected at every even length.
example (m : ℕ) :
    majorityDec (List.replicate m true ++ List.replicate m false) = false := by
  simp [majorityDec, List.filter_append]
  omega

-- One further true bit crosses the threshold.
example (m : ℕ) :
    majorityDec (true :: (List.replicate m true ++ List.replicate m false)) = true := by
  simp [majorityDec, List.filter_append]
  omega
