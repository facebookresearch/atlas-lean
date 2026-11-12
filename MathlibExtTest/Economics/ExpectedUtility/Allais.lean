/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Economics.ExpectedUtility.Allais
import Mathlib.Tactic

/-! # Tests for `MathlibExt.Economics.ExpectedUtility.Allais`

The Allais lotteries have the classical weights, and some complete transitive preference violates
independence. -/

open Convexity
open MathlibExt.Economics.ExpectedUtility
open MathlibExt.Economics.ExpectedUtility.Allais

namespace MathlibExtTest.Economics.ExpectedUtility.Allais

example : L2.weights 0 = 1 / 100 := L2_w0

example : L2.weights 1 = 89 / 100 := L2_w1

example : L2.weights 2 = 1 / 10 := L2_w2

example : L4.weights 0 = 9 / 10 := L4_w0

example : L4.weights 2 = 1 / 10 := L4_w2

example : ∃ R : StdSimplex ℝ Prize → StdSimplex ℝ Prize → Prop,
    IsPreferenceRelation R ∧ ¬ SatisfiesIndependence R := by
  obtain ⟨R, hR, h12, h43⟩ := exists_isPreferenceRelation_allais
  exact ⟨R, hR, not_satisfiesIndependence_of_allais h12 h43⟩

end MathlibExtTest.Economics.ExpectedUtility.Allais
