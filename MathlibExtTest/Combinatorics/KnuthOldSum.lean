/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.KnuthOldSum
import Mathlib.Tactic.NormNum

namespace MathlibExt.Combinatorics.KnuthOldSumWanted

-- The empty word has zero occurrences of the distinguished letter.
example : Nat.card {w : Fin 0 → Fin 4 //
    Even (Finset.univ.filter (fun i => w i = 0)).card} = 1 := by
  rw [card_evenACount_words]
  decide

-- Direct enumeration counts the nine words with no zero and the word with two zeros.
example : Nat.card {w : Fin 2 → Fin 4 //
    Even (Finset.univ.filter (fun i => w i = 0)).card} = 10 := by
  rw [Nat.card_eq_fintype_card]
  decide

example : knuthOldSumWeight 0 = 1 := by norm_num [knuthOldSumWeight]

end MathlibExt.Combinatorics.KnuthOldSumWanted
