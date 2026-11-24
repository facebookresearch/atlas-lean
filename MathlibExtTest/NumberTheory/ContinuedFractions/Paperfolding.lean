/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ContinuedFractions.Paperfolding
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt.paperfoldingSum_contFrac_cloitre_ruler

-- A zero divisor makes the terms zero from its first occurrence onward.
example : paperfoldingSumTerm (fun _ => 0) 2 = 0 := by simp [paperfoldingSumTerm]

-- Digits 3, 5, and 11 of the fractional part end the first, second, and fourth
-- letters. Their distinct values check both ruler indexing and the final crease.
private noncomputable def testSum := ∑' n, paperfoldingSumTerm (fun k => k + 2) n

example :
    (GenContFract.of testSum).partDens.get? 2 = some 2 ∧
    (GenContFract.of testSum).partDens.get? 4 = some 3 ∧
    (GenContFract.of testSum).partDens.get? 10 = some 4 := by
  have h := (paperfoldingSum_contFrac_cloitre_ruler (fun k => k + 2) rfl (by intro k; omega) 2).2
  have h₁ : padicValNat 2 1 = 0 := by simp [Nat.padicValNat_def]
  have h₂ : padicValNat 2 2 = 1 := by simp [Nat.padicValNat_def]
  have h₄ : padicValNat 2 4 = 2 := by
    rw [show 4 = 2 ^ 2 from rfl, Nat.padicValNat_def, Nat.multiplicity_prime_pow]
  simpa [testSum, cloitreCreaseInterleave_cloitreApprox_two, h₁, h₂, h₄] using
    And.intro (h 2 (by decide)) (And.intro (h 4 (by decide)) (h 10 (by decide)))

end MetaMathlibExt.paperfoldingSum_contFrac_cloitre_ruler
