/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Crypto.Framework.GenericGroup.RandomEncoding
import CSLibExt.Crypto.Framework.GenericGroup.PrimePowerAgreement
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.NormNum.Prime

/-! # Tests for the bit-string experiment and its prime-power collision estimate -/

namespace CSLibExtTest.Crypto.Framework.GenericGroup.RandomEncodingTests

open Cslib.Crypto.Framework Cslib.Crypto.Framework.GenericGroup RandomEncoding

-- The two encodings have identical equality patterns but opposite second bits on every label.
private def padded (tag : Bool) : Encoding 2 2 where
  toFun x := ![decide (x = 1), tag]
  inj' := by
    intro x y h
    have h₀ := congrFun h (0 : Fin 2)
    fin_cases x <;> fin_cases y <;> first | rfl | contradiction

-- Two group elements do not use up the four possible bit strings.
example (tag : Bool) : ¬ Function.Surjective (padded tag) := by
  intro hs
  obtain ⟨x, hx⟩ := hs (fun _ => !tag)
  have ht : tag = !tag := congrFun hx 1
  cases tag <;> contradiction

-- Read a bit from the identity reply, not an equality test. Both branches output a fixed value.
-- Only the longer branch uses the newly obtained handle as an operand of a second call.
private def inspectReply : Interaction 2 2 2 2 :=
  .query .identity fun word => if word 1 then
    .query (.compose (Fin.last 2) 0) fun _ => .output 0
  else .output 0

example : inspectReply.run (padded false) ![1, 1] = (0, 1) := by decide
example : inspectReply.run (padded true) ![1, 1] = (0, 2) := by decide

-- The two input handles need not be distinct; inversion uses the selected occurrence.
example (enc : Encoding 6 3) (x : ZMod 6) : enc 1 = enc x ↔ 1 = x := enc.injective.eq_iff
example : (Call.inverse (1 : Fin 2)).value ![(1 : ZMod 6), 2] = 4 := by decide
example : (Call.compose (1 : Fin 2) 1).value ![(1 : ZMod 6), 5] = 4 := by decide

-- Even with no calls the observer can use both full input strings, in the given order.
example {N n : ℕ} (enc : Encoding N n) (x : ZMod N) (f : (Fin n → Bool) → (Fin n → Bool) → ZMod N) :
    observedOutput (q := 0) (fun g t => .output (f g t)) enc x = f (enc 1) (enc x) := rfl

-- The budget can be feasible and the numerical bound informative for a composite order.
example : 2038 ≤ 2 ^ 11 ∧ 1 + 4 * Nat.clog 2 2038 = 45 ∧
    (2038 : ℕ).primeFactors.max' (Nat.nonempty_primeFactors.mpr (by decide)) = 1019 ∧
    (45 : ℝ) ^ 2 / (2 * 1019) < 1 := by
  refine ⟨by decide, by decide, ?_, by norm_num⟩
  have hf : (2038 : ℕ).primeFactors = {2, 1019} := by
    rw [show 2038 = 2 * 1019 by decide, Nat.primeFactors_mul (by decide) (by decide),
      Nat.prime_two.primeFactors, (by norm_num : Nat.Prime 1019).primeFactors]
    rfl
  simp [hf, Finset.max'_insert]

-- A biased or unbiased coin may select the output, but it cannot improve a blind guess.
example (coins : PMF Bool) : winProb ((experiment (N := 6) (n := 3) (q := 0) (by decide)
    (by decide) coins (fun r _ _ => .output (if r then 2 else 5))).map
    fun z => decide (z.2 = z.1)) = 1 / 6 :=
  winProb_of_secret_independent _ _ coins _ (fun r _ => if r then 2 else 5) (by intros; rfl)

-- Modulo nine the difference of the slopes can be a nonunit. A nonempty fiber can attain
-- the bound (three points), unlike the at-most-one estimate over a field.
example : (Finset.univ.filter fun x : ZMod 9 => affEval x (1, 3) = affEval x (4, 0)).card = 3 := by
  decide
example (u v : Aff (3 ^ (1 + 1))) (h : u ≠ v) :
    (Finset.univ.filter fun x => affEval x u = affEval x v).card ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact affEval_eq_card_le_primePow (e := 1) h

end CSLibExtTest.Crypto.Framework.GenericGroup.RandomEncodingTests
