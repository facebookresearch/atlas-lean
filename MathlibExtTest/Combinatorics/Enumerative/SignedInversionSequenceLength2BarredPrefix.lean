/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2BarredPrefix

/-! # Tests for relabelling the barred prefix of signed inversion sequences -/

namespace MetaMathlibExt.signedInvSeq_wilf_b0b1_b01_0b1_0b0.Tests

private abbrev leftPatterns : Finset SignedPattern2 :=
  {⟨.lt, true, true⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩, ⟨.eq, false, true⟩}

private abbrev rightPatterns : Finset SignedPattern2 :=
  {⟨.eq, true, true⟩, ⟨.lt, true, false⟩, ⟨.lt, false, true⟩, ⟨.eq, false, true⟩}

-- The barred prefix is constant on the left and increasing on the right. Each prefix contains
-- the pattern that the other class forbids, and an unbarred entry before a bar is forbidden.
example :
    let e : Fin 3 → ℕ × Bool := ![(0, true), (0, true), (0, false)]
    let f : Fin 3 → ℕ × Bool := ![(0, true), (1, true), (0, false)]
    let g : Fin 2 → ℕ × Bool := ![(0, false), (1, true)]
    (∀ p ∈ leftPatterns, ¬ SignedInvSeqContains e p) ∧
      SignedInvSeqContains e ⟨.eq, true, true⟩ ∧
    (∀ p ∈ rightPatterns, ¬ SignedInvSeqContains f p) ∧
      SignedInvSeqContains f ⟨.lt, true, true⟩ ∧
    SignedInvSeqContains g ⟨.lt, false, true⟩ := by
  unfold SignedInvSeqContains
  decide

-- Count the length-three avoiders on the left, `3! + 3`, and transfer the count to the right.
example : signedInvAvoidCount leftPatterns 3 = 9 ∧ signedInvAvoidCount rightPatterns 3 = 9 := by
  rw [← congrFun signedInvSeq_wilf_b0b1_b01_0b1_0b0 3, and_self]
  let word (a : (i : Fin 3) → Fin (i.val + 1) × Bool) (i : Fin 3) : ℕ × Bool :=
    ((a i).1.val, (a i).2)
  let good (a) := ∀ p ∈ leftPatterns, ¬ SignedInvSeqContains (word a) p
  let equiv : {e : Fin 3 → ℕ × Bool // (∀ i, (e i).1 ≤ i) ∧
      ∀ p ∈ leftPatterns, ¬ SignedInvSeqContains e p} ≃ {a // good a} := {
    toFun := fun ⟨e, bound, avoids⟩ =>
      ⟨fun i => (⟨(e i).1, Nat.lt_succ_of_le (bound i)⟩, (e i).2), avoids⟩
    invFun := fun a => ⟨word a.val, fun i => Nat.le_of_lt_succ (a.val i).1.isLt, a.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let : DecidablePred good := fun a => by
    unfold good SignedInvSeqContains
    infer_instance
  rw [signedInvAvoidCount, Nat.card_congr equiv, Nat.card_eq_fintype_card]
  decide

end MetaMathlibExt.signedInvSeq_wilf_b0b1_b01_0b1_0b0.Tests
