/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Feistel
public import CSLibExt.Crypto.SymmetricKey.Modes
public import Mathlib.Data.Fin.VecNotation

/-!
# Tests for Feistel rounds
-/

@[expose] public section

namespace Cslib.Crypto.FeistelTests

open Cslib.Crypto.Feistel

/-- With the zero round function, a round swaps the halves. -/
example : feistelRound (n := 1) (fun _ => fun _ => false)
    (fun _ => true, fun _ => false) = (fun _ => false, fun _ => true) := rfl

/-- With the identity round function, `(l, r) ↦ (r, l xor r)`. -/
example : feistelRound (n := 2) id (![true, false], ![true, true]) =
    (![true, true], ![false, true]) := by
  decide

/-- The inverse round recovers the block from the output above. -/
example : (feistelRound (n := 2) id).symm (![true, true], ![false, true]) =
    (![true, false], ![true, true]) := by
  decide

/-- A keyed three-round Feistel network is a block cipher in the sense of
`Cslib.Crypto.Modes.BlockCipher`. -/
example {K : Type} {n : ℕ} (F : K → Fin 3 → (Fin n → Bool) → (Fin n → Bool)) :
    Cslib.Crypto.Modes.BlockCipher K ((Fin n → Bool) × (Fin n → Bool)) :=
  fun k => feistelRound (F k 2) * feistelRound (F k 1) * feistelRound (F k 0)

end Cslib.Crypto.FeistelTests
