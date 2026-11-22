/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.RecursionTheorem

@[expose] public section

/-!
# Tests for self-reference through the recursion theorem
-/

set_option autoImplicit false

open Cslib.Decidability Encodable
open Nat.Partrec (Code)

namespace CSLibExtTest.Computability.Decidability.RecursionTheorem

/-- A quine: its output on `0` is its own number. -/
example : ∃ c : Code, c.eval 0 = Part.some (encode c) := by
  obtain ⟨c, hc⟩ := exists_quine
  exact ⟨c, hc 0⟩

/-- A code that halts on its own number and nowhere else. -/
example : ∃ c : Code, (c.eval (encode c)).Dom ∧ ¬(c.eval (encode c + 1)).Dom := by
  obtain ⟨c, hc⟩ := exists_dom_eq_singleton_encode
  refine ⟨c, ?_, ?_⟩
  · change encode c ∈ c.eval.Dom
    rw [hc]
    rfl
  · change encode c + 1 ∉ c.eval.Dom
    rw [hc]
    simp

/-- **Halting on input `0` is undecidable, by the recursion theorem**: the argument Sipser uses
for `A_TM`, applied to this fixed-input halting predicate. A decider would let a code ask whether
it halts and then do the opposite. (Mathlib states this as `ComputablePred.halting_problem`,
proved through Rice's theorem.) -/
example : ¬ComputablePred fun c : Code ↦ (c.eval 0).Dom := by
  rintro ⟨_, hd⟩
  obtain ⟨c, hc⟩ := Code.fixed_point₂
    (f := fun c _ ↦ cond (decide (c.eval 0).Dom) Part.none (Part.some 0))
    (Partrec.cond (hd.comp Computable.fst) Partrec.none (Partrec.const' _)).to₂
  by_cases h : (c.eval 0).Dom
  · have h' := h
    rw [hc] at h'
    simp [h] at h'
  · apply h
    rw [hc]
    simp [h]

/-- **Sipser, Theorem 6.8**, the fixed-point form, is Mathlib's `Nat.Partrec.Code.fixed_point`:
the transformation `c ↦ comp succ c` has a code computing the same function as its image. -/
example : ∃ c : Code, (Code.comp Code.succ c).eval = c.eval :=
  Code.fixed_point (Code.primrec₂_comp.comp (Primrec.const _) Primrec.id).to_comp

end CSLibExtTest.Computability.Decidability.RecursionTheorem
