/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Hash.MerkleDamgard
public import Mathlib.Data.ZMod.Basic

/-!
# Tests for the Merkle–Damgård transform

The compression function `h (z, x) = z + x` on `ZMod 7` (with `iv = 0` and the length block `L`)
is far from collision resistant, so the hash collides; `findCollision` recovers compression
collisions:
* `[1, 2]` and `[2, 1]` (same length): the walk back finds `h (1, 2) = h (2, 1)`.
* `[3]` and `[1, 1]` (different lengths): the final step gives `h (3, 1) = h (2, 2)`.
-/

@[expose] public section

namespace Cslib.Crypto.MerkleDamgardTests

open Cslib.Crypto.MerkleDamgard

/-- A (bad) compression function on `ZMod 7`. -/
def h (p : ZMod 7 × ZMod 7) : ZMod 7 := p.1 + p.2

/-- The length block. -/
def lenBlock (L : ℕ) : ZMod 7 := L

example : chain h 0 [1, 2, 3] = 6 := by decide

example : hash h 0 lenBlock [1, 2] = hash h 0 lenBlock [2, 1] := by decide

example : findCollision h 0 lenBlock [1, 2] [2, 1] = some ((1, 2), (2, 1)) := by decide

example : findCollision h 0 lenBlock [3] [1, 1] = some ((3, 1), (2, 2)) := by decide

example : ∃ p, findCollision h 0 lenBlock [1, 2] [2, 1] = some p ∧ IsCollision h p :=
  findCollision_spec h 0 lenBlock (by decide) (by decide) (fun _ => rfl)

theorem lenBlock_inj : ∀ L L', L < 7 → L' < 7 → lenBlock L = lenBlock L' → L = L' := by
  intro L L' hL hL' heq
  have := congrArg ZMod.val heq
  rwa [lenBlock, lenBlock, ZMod.val_natCast_of_lt hL, ZMod.val_natCast_of_lt hL'] at this

example (A : Bool → List (ZMod 7) × List (ZMod 7)) :
    hashCollisionGame h 0 lenBlock 7 A true ≤
      compressionCollisionGame h (reduction h 0 lenBlock A) true :=
  hashCollisionGame_le h 0 lenBlock 7 lenBlock_inj A

end Cslib.Crypto.MerkleDamgardTests
