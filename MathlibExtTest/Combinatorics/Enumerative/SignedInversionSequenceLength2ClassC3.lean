/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2ClassC3

/-! # Tests for signed inversion sequences in class C3 -/

namespace MetaMathlibExt.signedInvSeq_wilf_and_gf_b0b1_b0b0_b01_0b1.Tests

private abbrev firstPatterns : Finset SignedPattern2 :=
  {⟨.lt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩}

private abbrev secondPatterns : Finset SignedPattern2 :=
  {⟨.lt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩}

private abbrev thirdPatterns : Finset SignedPattern2 :=
  {⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, false, true⟩, ⟨.eq, false, true⟩}

example : signedInvAvoidCount firstPatterns 0 = 1 := by
  rw [signedInvSeq_wilf_and_gf_b0b1_b0b0_b01_0b1.2.2]
  decide

example : signedInvAvoidCount firstPatterns 3 = 10 ∧
    signedInvAvoidCount secondPatterns 3 = 10 ∧ signedInvAvoidCount thirdPatterns 3 = 10 := by
  have h := signedInvSeq_wilf_and_gf_b0b1_b0b0_b01_0b1
  rw [← h.2.1, ← h.1, h.2.2]
  decide

-- These two-letter words distinguish the three avoidance classes.
example :
    let a : Fin 2 → ℕ × Bool := ![(0, true), (0, false)]
    let b : Fin 2 → ℕ × Bool := ![(0, true), (0, true)]
    let c : Fin 2 → ℕ × Bool := ![(0, true), (1, true)]
    (∀ p ∈ firstPatterns, ¬ SignedInvSeqContains a p) ∧
      SignedInvSeqContains a ⟨.eq, true, false⟩ ∧
    (∀ p ∈ secondPatterns, ¬ SignedInvSeqContains b p) ∧
      SignedInvSeqContains b ⟨.eq, true, true⟩ ∧
    (∀ p ∈ thirdPatterns, ¬ SignedInvSeqContains c p) ∧
      SignedInvSeqContains c ⟨.lt, true, true⟩ := by
  unfold SignedInvSeqContains
  decide

end MetaMathlibExt.signedInvSeq_wilf_and_gf_b0b1_b0b0_b01_0b1.Tests
