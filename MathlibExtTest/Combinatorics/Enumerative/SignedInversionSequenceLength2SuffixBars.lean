/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import all MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2
import all MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2SuffixBars
import Mathlib.Tactic.FinCases

/-! # Tests for the signed inversion sequence suffix-bar bijection -/

namespace MetaMathlibExt.signedInvSeq_wilf_b1b0_b10_b0b0.Tests

open signedInvSeq_wilf_b1b0_b0b1_b00_b01_1b0 (Seen toggle)

-- The 1 at position 1 cannot be barred, since a 0 follows it. The bars on the
-- two eligible magnitudes extend independently, including over an intervening magnitude.
example : toggle (![ (0, true), (1, false), (0, false), (1, true), (1, false)] : Fin 5 → ℕ × Bool) =
    ![(0, true), (1, false), (0, true), (1, true), (1, true)] := by
  funext i
  fin_cases i <;> simp [toggle, Seen, Fin.exists_fin_succ]

example (single : Bool) :
    let e : Fin 5 → ℕ × Bool := ![(0, true), (1, false), (0, !single), (1, true), (1, !single)]
    (∀ p ∈ suffixPatterns single, ¬ SignedInvSeqContains e p) ∧
      SignedInvSeqContains e ⟨.eq, true, !single⟩ := by
  cases single <;> unfold SignedInvSeqContains <;> decide

-- The public result gives the equality at a length with repeated magnitudes.
example : signedInvAvoidCount (suffixPatterns true) 5 = signedInvAvoidCount (suffixPatterns false) 5 :=
  congrFun signedInvSeq_wilf_b1b0_b10_b0b0 5

end MetaMathlibExt.signedInvSeq_wilf_b1b0_b10_b0b0.Tests
