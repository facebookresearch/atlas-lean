/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SignedInversionSequenceLength2

/-! # Tests for signed inversion sequences avoiding length-2 patterns -/

namespace MetaMathlibExt.signedInvSeq_wilf_b1b0_b0b1_b00_b01_1b0.Tests

private abbrev forbidden (b : Bool) : Finset SignedPattern2 :=
  {⟨.gt, true, true⟩, ⟨.lt, true, true⟩, ⟨.eq, true, b⟩, ⟨.lt, true, false⟩, ⟨.gt, false, true⟩}

-- The empty word contributes the constant term even when all patterns are forbidden.
example : PowerSeries.coeff 0 (signedInvAvoidGF Finset.univ) = 1 := by
  simp [coeff_signedInvAvoidGF, signedInvAvoidCount_zero]

-- Two barred zeroes are allowed on the left. Removing the second bar gives a right avoider.
example (b : Bool) :
    let e := fun i : Fin 2 => (0, i == 0 || b)
    SignedInvSeqContains e ⟨.eq, true, b⟩ ∧ ∀ p ∈ forbidden (!b), ¬ SignedInvSeqContains e p := by
  cases b <;> unfold SignedInvSeqContains <;> decide

-- Independently enumerate the bounded entries at length two.
example (b : Bool) : signedInvAvoidCount (forbidden b) 2 = 5 := by
  let word (a : (i : Fin 2) → Fin (i.val + 1) × Bool) (i : Fin 2) : ℕ × Bool :=
    ((a i).1.val, (a i).2)
  let good (a) := ∀ p ∈ forbidden b, ¬ SignedInvSeqContains (word a) p
  let equiv : {e : Fin 2 → ℕ × Bool // (∀ i, (e i).1 ≤ i) ∧
      ∀ p ∈ forbidden b, ¬ SignedInvSeqContains e p} ≃ {a // good a} := {
    toFun := fun ⟨e, h, havoid⟩ => ⟨fun i => (⟨(e i).1, Nat.lt_succ_of_le (h i)⟩, (e i).2),
      havoid⟩
    invFun := fun a => ⟨word a.val, fun i => Nat.le_of_lt_succ (a.val i).1.isLt, a.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let : DecidablePred good := fun a => by
    unfold good SignedInvSeqContains
    infer_instance
  rw [signedInvAvoidCount, Nat.card_congr equiv, Nat.card_eq_fintype_card]
  cases b <;> decide

end MetaMathlibExt.signedInvSeq_wilf_b1b0_b0b1_b00_b01_1b0.Tests

namespace MetaMathlibExt.signedInvSeq_wilf_b1b0_b10_b0b1_b00_b01_0b0.Tests

private abbrev forbidden (b : Bool) : Finset SignedPattern2 :=
  {⟨.gt, true, true⟩, ⟨.gt, true, false⟩, ⟨.lt, true, true⟩, ⟨.eq, true, b⟩,
    ⟨.lt, true, false⟩, ⟨.eq, false, true⟩}

-- After an unbarred zero and a barred one, the sign of the last one selects the class.
example (b : Bool) :
    let e := fun i : Fin 3 => if i = 0 then (0, false) else (1, i == 1 || b)
    SignedInvSeqContains e ⟨.eq, true, b⟩ ∧ ∀ p ∈ forbidden (!b), ¬ SignedInvSeqContains e p := by
  cases b <;> unfold SignedInvSeqContains <;> decide

-- An unbarred zero followed later by a barred zero rules out both classes.
example (b : Bool) :
    let e := fun i : Fin 3 => (if i = 1 then 1 else 0, i == 2)
    ∃ p ∈ forbidden b, SignedInvSeqContains e p := by
  refine ⟨⟨.eq, false, true⟩, by simp [forbidden], 0, 2, ?_⟩
  decide

end MetaMathlibExt.signedInvSeq_wilf_b1b0_b10_b0b1_b00_b01_0b0.Tests
