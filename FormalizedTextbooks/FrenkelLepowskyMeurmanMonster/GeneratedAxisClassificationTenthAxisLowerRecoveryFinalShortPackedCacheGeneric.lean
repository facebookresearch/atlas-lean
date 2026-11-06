/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Int.Notation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerIncomingTree

/-! Ungated numerical candidate data/helper draft. Discovery is not a source proof. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Exact original address field of one packed candidate word. -/
def generatedTenthPackedSourceCacheKey (word : ℕ) : ℕ := word % 2 ^ 17

/-- Signed eight-bit candidate value, decoded without an unsigned sign convention. -/
def generatedTenthPackedSourceCacheValue (word : ℕ) : ℤ :=
  ((word / 2 ^ 17) % 256 : ℕ) - (128 : ℤ)

/-- Balanced word lookup returns an exact signed candidate value or the retained zero default. -/
def generatedTenthPackedSourceCacheLookup (t : GeneratedNinthIncomingTree ℕ) (a : ℕ) : ℤ :=
  match t.lookup generatedTenthPackedSourceCacheKey a with
  | none => 0
  | some word => generatedTenthPackedSourceCacheValue word

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
