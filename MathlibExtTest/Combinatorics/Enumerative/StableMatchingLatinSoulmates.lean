/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fintype.Perm
import MathlibExt.Combinatorics.Enumerative.StableMatchingLatinSoulmates

namespace MetaMathlibExt.StableMatchingSequences

open Nat

private theorem latinSquareCount_two : latinSquareCount 2 = 2 := by
  let : DecidablePred (fun M : Fin 2 → Equiv.Perm (Fin 2) =>
      ∀ r : Fin 2, Function.Injective fun i => M i r) := fun M =>
    inferInstanceAs (Decidable (∀ r i i' : Fin 2, M i r = M i' r → i = i'))
  rw [latinSquareCount, Nat.card_eq_fintype_card]
  decide

example :
    Nat.card {P : PreferenceProfile 2 //
        (∀ r : Fin 2, Function.Injective fun i => P.1 i r) ∧ soulmatePairCount P = 1} = 4 := by
  rw [men_latin_soulmate_profiles_card (n := 2) (k := 1), latinSquareCount_two]
  decide

example :
    Nat.card {P : PreferenceProfile 0 //
        (∀ r : Fin 0, Function.Injective fun i => P.1 i r) ∧ soulmatePairCount P = 0} = 1 := by
  rw [men_latin_soulmate_profiles_card (n := 0) (k := 0), latinSquareCount_zero]
  decide

example :
    Nat.card {P : PreferenceProfile 1 //
        (∀ r : Fin 1, Function.Injective fun i => P.1 i r) ∧ soulmatePairCount P = 2} = 0 := by
  rw [men_latin_soulmate_profiles_card (n := 1) (k := 2)]
  simp

end MetaMathlibExt.StableMatchingSequences
