/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.ComputationalBiology.CherryDistribution
import Mathlib.Tactic.NormNum

/-! # Tests for the mean cherry count -/

namespace DomainsTest.Biology.ComputationalBiology.CherryDistribution

open WantedExt.Biology.ComputationalBiology.CherryDistributionWanted

example : cherryMean 4 = 2 := by
  rw [cherryMean_eq 4 (by decide)]
  norm_num

example : cherryMean 6 = (15 : ℝ) / 7 := by
  rw [cherryMean_eq 6 (by decide)]
  norm_num

end DomainsTest.Biology.ComputationalBiology.CherryDistribution

#check @WantedExt.Biology.ComputationalBiology.CherryDistributionWanted.cherryMean_eq
#print axioms WantedExt.Biology.ComputationalBiology.CherryDistributionWanted.cherryMean_eq
