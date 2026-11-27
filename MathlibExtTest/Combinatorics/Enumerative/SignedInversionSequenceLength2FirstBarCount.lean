/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2FirstBarCount

/-! # Tests for the signed inversion sequence count by the first bar -/

namespace MetaMathlibExt.signedInvSeq_wilf_and_count_b0b1_b0b0_b01.Tests

private abbrev leftPatterns : Finset SignedPattern2 :=
  {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩}

private abbrev rightPatterns : Finset SignedPattern2 :=
  {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩}

example : signedInvAvoidCount leftPatterns 0 = 1 := by
  rw [signedInvSeq_wilf_and_count_b0b1_b0b0_b01.2]
  decide

example : signedInvAvoidCount leftPatterns 3 = 17 ∧ signedInvAvoidCount rightPatterns 3 = 17 := by
  have h : signedInvAvoidCount leftPatterns 3 = 17 := by
    rw [signedInvSeq_wilf_and_count_b0b1_b0b0_b01.2]
    decide
  exact ⟨h, (congrFun signedInvSeq_wilf_and_count_b0b1_b0b0_b01.1 3).symm.trans h⟩

-- After a barred zero, the equal-magnitude entry must be unbarred on the left and barred
-- on the right.
example :
    let e : Fin 2 → ℕ × Bool := ![(0, true), (0, false)]
    let f : Fin 2 → ℕ × Bool := ![(0, true), (0, true)]
    (∀ p ∈ leftPatterns, ¬ SignedInvSeqContains e p) ∧
      SignedInvSeqContains e ⟨.eq, true, false⟩ ∧
    (∀ p ∈ rightPatterns, ¬ SignedInvSeqContains f p) ∧
      SignedInvSeqContains f ⟨.eq, true, true⟩ := by
  unfold SignedInvSeqContains
  decide

end MetaMathlibExt.signedInvSeq_wilf_and_count_b0b1_b0b0_b01.Tests
