/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2Harmonic

/-! # Tests for the harmonic count of signed inversion sequences -/

namespace MetaMathlibExt.signedInvSeq_wilf_and_count_b0b1_b0b0_0b1.Tests

private abbrev firstPatterns : Finset SignedPattern2 :=
  {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, false, true⟩}

private abbrev secondPatterns : Finset SignedPattern2 :=
  {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩}

private abbrev thirdPatterns : Finset SignedPattern2 :=
  {⟨.lt, true, true⟩, ⟨.lt, false, true⟩, ⟨.eq, false, true⟩}

example : signedInvAvoidCount firstPatterns 0 = 1 := by
  have h := signedInvSeq_wilf_and_count_b0b1_b0b0_0b1.2.2 0
  norm_num at h
  exact_mod_cast h

example : signedInvAvoidCount firstPatterns 3 = 17 ∧
    signedInvAvoidCount secondPatterns 3 = 17 ∧ signedInvAvoidCount thirdPatterns 3 = 17 := by
  have h := signedInvSeq_wilf_and_count_b0b1_b0b0_0b1
  have h₃ := h.2.2 3
  norm_num [harmonic_succ, Nat.factorial_succ] at h₃
  rw [← h.2.1, ← h.1]
  have hc : signedInvAvoidCount firstPatterns 3 = 17 := by exact_mod_cast h₃
  exact ⟨hc, hc, hc⟩

end MetaMathlibExt.signedInvSeq_wilf_and_count_b0b1_b0b0_0b1.Tests
