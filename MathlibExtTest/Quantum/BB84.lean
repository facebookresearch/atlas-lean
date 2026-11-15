/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.BB84

/-!
# Tests for the BB84 intercept-resend error event

Concrete rounds with Alice and Bob in the Z basis (`false`): an error when Eve measures in the X
basis and Bob's coin differs from Alice's bit, no error when it agrees, no error when Eve measures
in Alice's basis, and no error in an unsifted round.
-/

@[expose] public section

/-- Eve measures in the X basis: her result is her coin, Bob's result is his coin `true`, and it
differs from Alice's bit `false`. -/
example : bb84BobResult (bb84EveResult false false true true) true false true = true := rfl

example : bb84Error false true false true false = true := rfl

/-- The same round with Bob's coin equal to Alice's bit has no error. -/
example : bb84Error false false false true false = false := rfl

/-- Eve measures in Alice's basis: Bob reads Alice's bit `true` back without using his coin, so
the round has no error. -/
example : bb84BobResult (bb84EveResult true false false false) false false false = true := rfl

example : bb84Error true false false false false = false :=
  bb84_no_error_when_eve_correct true false false false

/-- An unsifted round (Bob in the X basis) is never an error. -/
example : bb84Error false true false true true = false := rfl

end
