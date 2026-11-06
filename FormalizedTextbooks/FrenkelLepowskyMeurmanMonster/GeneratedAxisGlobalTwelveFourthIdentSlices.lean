/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveFourthIdentChunk

/-! # Consecutive slices of a list

`slices L bs` cuts `L` into consecutive pieces of the lengths `bs` followed by the rest; the
pieces concatenate back to `L` (`slices_flatten`).  Chunked short transport checks of a long
literal source list use its slices directly, without a literal copy. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false

/-- Consecutive pieces of the lengths `bs`, followed by the rest. -/
def slices {α : Type} : List α → List ℕ → List (List α)
  | L, [] => [L]
  | L, b :: bs => L.take b :: slices (L.drop b) bs

/-- The slices concatenate back to the list. -/
theorem slices_flatten {α : Type} : ∀ (L : List α) (bs : List ℕ), (slices L bs).flatten = L
  | L, [] => by simp [slices]
  | L, b :: bs => by
    rw [slices, List.flatten_cons, slices_flatten (L.drop b) bs, List.take_append_drop]

/-- The number of slices. -/
theorem slices_length {α : Type} : ∀ (L : List α) (bs : List ℕ), (slices L bs).length = bs.length + 1
  | L, [] => by simp [slices]
  | L, b :: bs => by simp [slices, slices_length (L.drop b) bs]

end GeneratedAxisGlobalTwelveFourthIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
