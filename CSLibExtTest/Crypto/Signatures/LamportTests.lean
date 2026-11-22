/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Signatures.Lamport

/-!
# Tests for Lamport one-time signatures

* With the toy function `f x = x % 3` from `Fin 6` to `Fin 3`, an honest signature verifies, and
  the same signature does not verify for a message with a flipped bit.
* The security reduction is instantiated for a forger on two-bit messages.
* On one-bit messages over `Unit` (where every candidate signature verifies), the forger that
  requests `false` and forges `true` wins with probability `1`; the inverter built from it aborts
  when `(0, false)` is planted and returns a preimage when `(0, true)` is planted.
-/

@[expose] public section

namespace Cslib.Crypto.LamportTests

open Cslib.Crypto.Signatures.Lamport

/-- A toy function `Fin 6 → Fin 3`. -/
def f (x : Fin 6) : Fin 3 := ⟨x.val % 3, Nat.mod_lt _ (by norm_num)⟩

/-- A toy secret key for two-bit messages. -/
def sk : Fin 2 × Bool → Fin 6
  | (0, false) => 0
  | (0, true) => 1
  | (1, false) => 2
  | (1, true) => 4

/-- The message `(true, false)`. -/
def m : Fin 2 → Bool := ![true, false]

example : Verify f (publicKey f sk) m (sign sk m) := verify_sign f sk m

/-- The signature on `m` does not verify for the message with the first bit flipped. -/
example : ¬Verify f (publicKey f sk) ![false, false] (sign sk m) := by decide

example (A : Forger (Fin 6) (Fin 3) Bool 2) :
    (forgeGame f A true).toReal ≤ 2 * 2 * (invertGame f (invert f A) true).toReal := by
  simpa using forgeGame_le f A

/-- The identity on `Unit`: every candidate signature verifies. -/
def trivialF (x : Unit) : Unit := x

/-- Request `false`, then forge on the distinct message `true`. -/
def alwaysForge : Forger Unit Unit Unit 1 where
  choose := fun _ _ _ => false
  forge := fun _ _ _ => (fun _ => true, fun _ => ())

/-- The only secret key over `Unit`. -/
def unitSk : Fin 1 × Bool → Unit := fun _ => ()

theorem true_ne_false_fun : (fun _ : Fin 1 => true) ≠ fun _ => false := by
  intro h
  have := congrFun h 0
  contradiction

example : alwaysForge.Wins trivialF unitSk () := by
  simp [Forger.Wins, alwaysForge, trivialF, publicKey, Verify, unitSk, true_ne_false_fun]

example : forgeGame trivialF alwaysForge true = 1 := by
  simp [forgeGame, Forger.Wins, alwaysForge, trivialF, publicKey, Verify, true_ne_false_fun]

/-- Planting at `(0, false)`, the requested bit: the inverter aborts. -/
example : invert trivialF alwaysForge () ((0, false), unitSk, ()) = none := rfl

/-- Planting at `(0, true)`, the forged bit: the inverter returns `σ' 0`. -/
example : invert trivialF alwaysForge () ((0, true), unitSk, ()) = some () := rfl

end Cslib.Crypto.LamportTests
