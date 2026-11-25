/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2FirstBars

/-! # Tests for copying bars from first occurrences in signed inversion sequences -/

namespace MetaMathlibExt.signedInvSeq_wilf_b1b0_b10_b0b0_0b0.Tests

private abbrev forbidden (single : Bool) : Finset SignedPattern2 :=
  {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.eq, true, single⟩, ⟨.eq, false, true⟩}

-- A zero repeats after an intervening one, and a two repeats immediately.
-- Copying the two first-occurrence bars switches which equal-letter pattern occurs.
example (single : Bool) :
    let e : Fin 5 → ℕ × Bool := ![(0, true), (1, false), (0, !single), (2, true), (2, !single)]
    (∀ p ∈ forbidden single, ¬ SignedInvSeqContains e p) ∧
      SignedInvSeqContains e ⟨.eq, true, !single⟩ := by
  cases single <;> unfold SignedInvSeqContains <;> decide

-- Count all bounded words at length three and transfer the result across the equivalence.
example : signedInvAvoidCount (forbidden true) 3 = 24 ∧
    signedInvAvoidCount (forbidden false) 3 = 24 := by
  rw [← congrFun signedInvSeq_wilf_b1b0_b10_b0b0_0b0 3, and_self]
  let word (a : (i : Fin 3) → Fin (i.val + 1) × Bool) (i : Fin 3) : ℕ × Bool :=
    ((a i).1.val, (a i).2)
  let good (a) := ∀ p ∈ forbidden true, ¬ SignedInvSeqContains (word a) p
  let equiv : {e : Fin 3 → ℕ × Bool // (∀ i, (e i).1 ≤ i) ∧
      ∀ p ∈ forbidden true, ¬ SignedInvSeqContains e p} ≃ {a // good a} := {
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

end MetaMathlibExt.signedInvSeq_wilf_b1b0_b10_b0b0_0b0.Tests
