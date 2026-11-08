/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Identification.Schnorr
public import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for Schnorr identification

In `ZMod 5` written multiplicatively, with generator `g = ofAdd 1`, secret key `x = 3` and
commitment randomness `k = 2`: the answers to the challenges `1` and `4` are `0` and `4`, both
transcripts are accepted, and the extractor recovers `x = 3` from them. The zero-knowledge
simulation identity is instantiated.
-/

@[expose] public section

namespace Cslib.Crypto.SchnorrTests

open Cslib.Crypto.PublicKey Cslib.Crypto.Identification.Schnorr

/-- `ZMod 5`, written multiplicatively. -/
abbrev G5 := Multiplicative (ZMod 5)

/-- The generator. -/
abbrev g : G5 := Multiplicative.ofAdd 1

theorem g_pow : g ^ 5 = 1 := by decide

example : respond (3 : ZMod 5) 2 1 = 0 ∧ respond (3 : ZMod 5) 2 4 = 4 := by decide

example : Accepts g (gpow g (3 : ZMod 5)) (gpow g (2 : ZMod 5)) (1 : ZMod 5) 0 :=
  accepts_honest g_pow 3 2 1

example : Accepts g (gpow g (3 : ZMod 5)) (gpow g (2 : ZMod 5)) (4 : ZMod 5) 4 :=
  accepts_honest g_pow 3 2 4

/-- The extractor recovers the secret key from the two transcripts: `(0 - 4) / (1 - 4) = 3`. -/
example : extract (1 : ZMod 5) 0 4 4 = 3 := by
  rw [extract, show (1 : ZMod 5) - 4 = 2 by decide, ZMod.inv_eq_of_mul_eq_one 5 2 3 (by decide)]
  decide

example : gpow g (extract (1 : ZMod 5) 0 4 4) = gpow g (3 : ZMod 5) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact extract_spec g_pow (gpow_pow_eq_one g_pow 3) (by decide)
    (accepts_honest g_pow 3 2 1) (accepts_honest g_pow 3 2 4)

example (x : ZMod 5) : transcript g x = simulate g (gpow g x) :=
  transcript_eq_simulate g_pow x

end Cslib.Crypto.SchnorrTests
