/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2ClassC45

/-! # Tests for the signed inversion sequences in class C45 -/

namespace MetaMathlibExt.signedInvSeq_wilf_b1b0_b0b0_b01_01.Tests

private abbrev leftPatterns : Finset SignedPattern2 :=
  {⟨.gt, true, true⟩, ⟨.eq, true, true⟩, ⟨.lt, true, false⟩, ⟨.lt, false, false⟩}

private abbrev rightPatterns : Finset SignedPattern2 :=
  {⟨.gt, true, true⟩, ⟨.eq, true, false⟩, ⟨.lt, true, false⟩, ⟨.eq, false, false⟩}

-- At the fourth position, the strict sequence has an unbarred zero and the weak one a barred one.
example :
    let e : Fin 5 → ℕ × Bool := ![(0, false), (0, false), (1, true), (0, false), (2, true)]
    let f : Fin 5 → ℕ × Bool := ![(0, false), (1, false), (1, true), (1, true), (2, true)]
    (∀ p ∈ leftPatterns, ¬ SignedInvSeqContains e p) ∧ SignedInvSeqContains e ⟨.eq, false, false⟩ ∧
    (∀ p ∈ rightPatterns, ¬ SignedInvSeqContains f p) ∧
      SignedInvSeqContains f ⟨.eq, true, true⟩ := by
  unfold SignedInvSeqContains
  decide

-- Enumerate the 48 signed inversion sequences at length three and transfer the count.
example : signedInvAvoidCount leftPatterns 3 = 14 ∧ signedInvAvoidCount rightPatterns 3 = 14 := by
  rw [← congrFun signedInvSeq_wilf_b1b0_b0b0_b01_01 3, and_self]
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

end MetaMathlibExt.signedInvSeq_wilf_b1b0_b0b0_b01_01.Tests
