/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.HardnessCircuitMachine

/-!
# Reading entries of the sequential gate computations

Weft, depth, and Boolean evaluation append one entry after each gate. A gate's
entry is computed from its strict prefix and these earlier entries persist in
the final table.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized.CircuitNormalMachine

open Cslib.Complexity.Classes

/-- All values obtained by applying each row's step to the preceding table. -/
def history {A B : Type*} (f : List A → B → A) (xs : List B) : List A :=
  xs.foldl (fun acc x => acc ++ [f acc x]) []

private theorem fold_props {A B : Type*} (f : List A → B → A) (xs : List B) (init : List A) :
    ∃ tail, tail.length = xs.length ∧
      xs.foldl (fun acc x => acc ++ [f acc x]) init = init ++ tail := by
  induction xs generalizing init with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons x xs ih =>
    obtain ⟨tail, ht, htail⟩ := ih (init ++ [f init x])
    exact ⟨f init x :: tail, by simp [ht], by simp [htail]⟩

@[simp] theorem length_history {A B : Type*} (f : List A → B → A) (xs : List B) :
    (history f xs).length = xs.length := by
  obtain ⟨tail, hl, ht⟩ := fold_props f xs []
  simpa only [history, ht, List.nil_append] using hl

private theorem getD_take_history {A B : Type*} (f : List A → B → A) (xs : List B) (d : A)
    (k i : ℕ) (hi : i < min k xs.length) :
    (history f (xs.take k)).getD i d = (history f xs).getD i d := by
  have hx : (xs.take k ++ xs.drop k).foldl (fun acc x => acc ++ [f acc x]) [] = history f xs :=
    by rw [List.take_append_drop]; rfl
  rw [List.foldl_append] at hx
  obtain ⟨tail, _, ht⟩ := fold_props f (xs.drop k) (history f (xs.take k))
  have h := hx.symm.trans ht
  rw [h, List.getD_append _ _ _ _]
  simpa using hi

/-- At a predecessor of a topologically ordered gate, reading the strict prefix gives the same
value as reading the full table. -/
theorem getD_history_prefix {A B : Type*} (f : List A → B → A) (xs : List B) (d : A)
    {k i : ℕ} (hk : k ≤ xs.length) (hi : i < k) :
    (history f (xs.take k)).getD i d = (history f xs).getD i d :=
  getD_take_history f xs d k i (by omega)

/-- Retrieve the equation defining one sequential entry. -/
theorem getD_history_gate {A B : Type*} (f : List A → B → A) (xs : List B) (d : A)
    (i : ℕ) (hi : i < xs.length) :
    (history f xs).getD i d = f (history f (xs.take i)) xs[i] := by
  rw [← getD_history_prefix f xs d (k := i+1) (by omega) (by omega),
    List.take_succ_eq_append_getElem hi]
  have hlen : (history f (xs.take i)).length = i := by simp [Nat.min_eq_left hi.le]
  change (((xs.take i) ++ [xs[i]]).foldl (fun acc x => acc ++ [f acc x]) []).getD i d = _
  rw [List.foldl_append]; change ((history f (xs.take i)) ++ [_]).getD i d = _
  simp [List.getD_eq_getElem?_getD, hlen]; rfl

/-- The history of gate values in the circuit evaluator. -/
theorem eval_history (C : List WCGate) (a : List Bool) :
    wcCircuitEval C a = history
      (fun vs g => gateValue vs (fun i : Fin a.length => a.getD i.val false) (acGateOfPair g))
      C := by
  simp [wcCircuitEval, circuitEval, history, List.foldl_map]

/-- The synchronous table from any positive round has exactly one row per gate. -/
@[simp] theorem table_length (n : ℕ) (C : List WCGate) (d : ℕ) :
    (table n C (d+1)).length = C.length := by simp [table]

/-- Read a specified polarity of an entry after one more round. -/
theorem table_getD (n : ℕ) (C : List WCGate) (d i : ℕ) (hi : i < C.length) (p : Bool) :
    atPolarity p ((table n C (d+1)).getD i falseNode) = gate n (table n C d) C[i] p := by
  cases p <;> simp [table, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, atPolarity]

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized.CircuitNormalMachine
