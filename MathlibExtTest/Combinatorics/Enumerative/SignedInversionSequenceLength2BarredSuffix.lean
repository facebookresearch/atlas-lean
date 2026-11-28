/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2BarredSuffix

/-! # Tests for the seven-pattern Wilf-equivalence -/

namespace MetaMathlibExt.signedInvSeq_wilf_b1b0_b10_b0b1_b0b0_b00_b01_1b0.Tests

private abbrev leftPatterns : Finset SignedPattern2 :=
  {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩,
    ⟨.eq, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩, ⟨.gt, false, true⟩}

private abbrev rightPatterns : Finset SignedPattern2 :=
  {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, true⟩,
    ⟨.eq, true, false⟩, ⟨.lt, true, false⟩, ⟨.eq, false, true⟩, ⟨.gt, false, true⟩}

-- A final bar can tie an earlier unbarred entry on the left. An increasing barred suffix
-- can occupy the whole word on the right.
example :
    let e : Fin 3 → ℕ × Bool := ![(0, false), (0, false), (0, true)]
    let f : Fin 3 → ℕ × Bool := ![(0, true), (1, true), (2, true)]
    (∀ p ∈ leftPatterns, ¬ SignedInvSeqContains e p) ∧
    SignedInvSeqContains e ⟨.eq, false, true⟩ ∧
    (∀ p ∈ rightPatterns, ¬ SignedInvSeqContains f p) ∧
    SignedInvSeqContains f ⟨.lt, true, true⟩ := by
  unfold SignedInvSeqContains
  decide

-- Count the six unbarred and five barred avoiders on the left and transfer the count.
example : signedInvAvoidCount rightPatterns 3 = 11 := by
  rw [← congrFun signedInvSeq_wilf_b1b0_b10_b0b1_b0b0_b00_b01_1b0 3]
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

end MetaMathlibExt.signedInvSeq_wilf_b1b0_b10_b0b1_b0b0_b00_b01_1b0.Tests
