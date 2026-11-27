/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2LastBars

/-! # Tests for the two four-pattern Wilf-equivalences proved by retaining last bars -/

namespace MetaMathlibExt.signedInvSeq_wilf_b1b0_b0b1_b0b0_1b0.Tests

private abbrev BoundedWord := (i : Fin 3) → Fin (i.val + 1) × Bool

private def word (a : BoundedWord) (i : Fin 3) : ℕ × Bool :=
  ((a i).1.val, (a i).2)

private def avoids (B : Finset SignedPattern2) (a : BoundedWord) : Prop :=
  ∀ p ∈ B, ¬ SignedInvSeqContains (word a) p

private instance decidableAvoids (B : Finset SignedPattern2) : DecidablePred (avoids B) :=
  fun a => by
    unfold avoids SignedInvSeqContains
    infer_instance

private theorem count_eq_fintype_card (B : Finset SignedPattern2) :
    signedInvAvoidCount B 3 = Fintype.card {a // avoids B a} := by
  let equiv : {e : Fin 3 → ℕ × Bool // (∀ i, (e i).1 ≤ i) ∧
      ∀ p ∈ B, ¬ SignedInvSeqContains e p} ≃ {a // avoids B a} := {
    toFun := fun ⟨e, bound, h⟩ =>
      ⟨fun i => (⟨(e i).1, Nat.lt_succ_of_le (bound i)⟩, (e i).2), h⟩
    invFun := fun a => ⟨word a.val, fun i => Nat.le_of_lt_succ (a.val i).1.isLt, a.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [signedInvAvoidCount, Nat.card_congr equiv, Nat.card_eq_fintype_card]

-- Enumerate the length-three avoiders on the left of each equivalence.
-- The two different counts distinguish the two pairs of pattern sets.
example :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, false, true⟩,
      ⟨.gt, false, true⟩} 3 = 23 := by
  rw [← congrFun signedInvSeq_wilf_b1b0_b0b1_b0b0_1b0.1 3, count_eq_fintype_card]
  decide

example :
    signedInvAvoidCount {⟨.gt, true, true⟩, ⟨.eq, true, false⟩, ⟨.eq, false, true⟩,
      ⟨.gt, false, true⟩} 3 = 24 := by
  rw [← congrFun signedInvSeq_wilf_b1b0_b0b1_b0b0_1b0.2 3, count_eq_fintype_card]
  decide

end MetaMathlibExt.signedInvSeq_wilf_b1b0_b0b1_b0b0_1b0.Tests
