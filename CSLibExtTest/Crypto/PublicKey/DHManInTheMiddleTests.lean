/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.PublicKey.DHManInTheMiddle

/-!
# Tests for the man-in-the-middle attack on Diffie–Hellman key agreement

* In `(ZMod 23)ˣ` with `g = 5`, which has order `22`, Alice's secret `a = 4` and Bob's secret
  `b = 3` give the honest key `18`. An adversary with exponents `a' = 7` and `b' = 2` sends Bob
  `5 ^ 7 = 17` and Alice `5 ^ 2 = 2`. Alice then outputs `2 ^ 4 = 16`, which the adversary
  computes as `(5 ^ 4) ^ 2 = 4 ^ 2`, and Bob outputs `17 ^ 3 = 14`, which it computes as
  `(5 ^ 3) ^ 7 = 10 ^ 7`. Alice's and Bob's keys differ.
* Replacing one message suffices for the keys to differ: with `a' = a` and `b' = 2 ≠ b`, Alice
  outputs `16` and Bob the honest key `18`; with `a' = 7 ≠ a` and `b' = b`, Alice outputs `18`
  and Bob `14`.
* When `g ^ q = 1`, Alice's and Bob's keys are `g ^ (a b')` and `g ^ (a' b)`.
* With `a' = a` and `b' = b` the attack is the honest exchange, and the statement gives back
  `aliceKey_eq_bobKey`.
-/

@[expose] public section

namespace Cslib.Crypto.DHManInTheMiddleTests

open Cslib.Crypto.PublicKey Cslib.Crypto.PublicKey.DHSecurity

/-! ### A concrete attack in `(ZMod 23)ˣ` -/

/-- The element `5` of `(ZMod 23)ˣ`, of order `22`; its inverse is `14`. -/
def five : (ZMod 23)ˣ := ⟨5, 14, by decide, by decide⟩

/-- `5` has order `22` in `(ZMod 23)ˣ`: `5 ^ 11 = -1`, `5 ^ 2 ≠ 1` and `5 ^ 22 = 1`. -/
example : (five ^ 11).val = 22 ∧ (five ^ 2).val ≠ 1 ∧ five ^ 22 = 1 := by decide

/-- The honest transcript, with Alice's secret `a = 4` and Bob's secret `b = 3`. -/
abbrev honest : (ZMod 23)ˣ × (ZMod 23)ˣ := transcript five (4 : ZMod 22) 3

/-- The adversary's transcript, with its exponents `a' = 7` and `b' = 2`. -/
abbrev forged : (ZMod 23)ˣ × (ZMod 23)ˣ := transcript five (7 : ZMod 22) 2

/-- The honest exchange: Alice sends `4`, Bob sends `10`, and both output `18`. -/
example : (honest.1.val, honest.2.val) = (4, 10) ∧
    (aliceKey (4 : ZMod 22) honest.2).val = 18 ∧ (bobKey (3 : ZMod 22) honest.1).val = 18 := by
  decide

/-- The adversary's messages: Bob receives `5 ^ 7 = 17` and Alice `5 ^ 2 = 2`. -/
example : (forged.1.val, forged.2.val) = (17, 2) := by decide

/-- Under the attack, Alice outputs `16`, and the adversary computes `16` from `b' = 2` and
Alice's message. -/
example : (aliceKey (4 : ZMod 22) forged.2).val = 16 ∧
    (bobKey (2 : ZMod 22) honest.1).val = 16 := by
  decide

/-- Under the attack, Bob outputs `14`, and the adversary computes `14` from `a' = 7` and Bob's
message. -/
example : (bobKey (3 : ZMod 22) forged.1).val = 14 ∧
    (aliceKey (7 : ZMod 22) honest.2).val = 14 := by
  decide

/-- The same equalities from `aliceKey_bobKey_man_in_the_middle`, with no computation. -/
example : aliceKey (4 : ZMod 22) forged.2 = bobKey (2 : ZMod 22) honest.1 ∧
    bobKey (3 : ZMod 22) forged.1 = aliceKey (7 : ZMod 22) honest.2 :=
  aliceKey_bobKey_man_in_the_middle five 4 3 7 2

/-- Under the attack, Alice's and Bob's keys differ (`16 ≠ 14`). -/
example : aliceKey (4 : ZMod 22) forged.2 ≠ bobKey (3 : ZMod 22) forged.1 := by decide

/-- Replacing only Bob's message (`a' = a = 4`, `b' = 2`) already separates the keys: Alice
outputs `16` and Bob the honest key `18`. -/
example : (aliceKey (4 : ZMod 22) (transcript five (4 : ZMod 22) 2).2).val = 16 ∧
    (bobKey (3 : ZMod 22) (transcript five (4 : ZMod 22) 2).1).val = 18 := by
  decide

/-- Replacing only Alice's message (`a' = 7`, `b' = b = 3`) already separates the keys: Alice
outputs the honest key `18` and Bob `14`. -/
example : (aliceKey (4 : ZMod 22) (transcript five (7 : ZMod 22) 3).2).val = 18 ∧
    (bobKey (3 : ZMod 22) (transcript five (7 : ZMod 22) 3).1).val = 14 := by
  decide

/-! ### The general statement -/

section General

variable {G : Type*} [CommGroup G] {q : ℕ} (g : G)

/-- When `g ^ q = 1`, as for a generator of a cyclic group of order `q`, Alice's key under the
attack is `g ^ (a b')` and Bob's is `g ^ (a' b)`. -/
example (hg : g ^ q = 1) (a b a' b' : ZMod q) :
    aliceKey a (transcript g a' b').2 = gpow g (a * b') ∧
      bobKey b (transcript g a' b').1 = gpow g (a' * b) :=
  ⟨dh_key_eq hg a b', (gpow_mul hg a' b).symm⟩

/-- Without interference (`a' = a`, `b' = b`), the statement is the correctness of the honest
exchange. -/
example (a b : ZMod q) : aliceKey a (transcript g a b).2 = bobKey b (transcript g a b).1 :=
  (aliceKey_bobKey_man_in_the_middle g a b a b).1

end General

end Cslib.Crypto.DHManInTheMiddleTests
