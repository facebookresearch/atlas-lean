/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Economics.Finance.ValueOfInformation

/-! # Perfect-information option value with a single feasible action -/

open MathlibExt.Probability.Decision.ValueOfInformation (evii)
open MathlibExt.Economics.Finance.ValueOfInformation (evii_diagonal_eq_optionValue_sub)
open MathlibExt.Economics.Finance.RealOptionValue
open MathlibExt.Probability.FiniteProbability

example (p : Bool → ℝ) (hp : ∀ s, 0 ≤ p s) (U : Unit → Bool → ℝ) :
    evii ({()} : Finset Unit) (by simp) (fun s e => if e = s then p s else 0) U = 0 := by
  rw [evii_diagonal_eq_optionValue_sub p hp U]
  simp [optionValue]
