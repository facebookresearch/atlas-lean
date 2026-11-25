/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.GijswijtProperPrefixes

open MetaMathlibExt

-- The first block has just the empty proper prefix.
example {m : ℕ} (hm : 1 ≤ m) (P : List ℕ) :
    (P <+: gijswijtBlock (m + 1) 1 ∧ P.length < (gijswijtBlock (m + 1) 1).length ∧
        curlingNumber P ≤ m + 1) ↔ P = [] := by
  rw [gijswijtProperPrefix_curling_iff hm le_rfl]
  constructor
  · rintro ⟨a, _, h⟩
    simpa only [gijswijtBlockWord_one] using h
  · intro h
    exact ⟨fun _ => 0, by omega, h.trans (gijswijtBlockWord_one _ _).symm⟩

-- The maximal allowed exponent occurs among the proper prefixes of the second block.
example :
    [2, 2] <+: gijswijtBlock 2 2 ∧ [2, 2].length < (gijswijtBlock 2 2).length ∧
      curlingNumber [2, 2] ≤ 2 := by
  apply (gijswijtProperPrefix_curling_iff (m := 1) (u := 2) (by decide) (by decide) _).mpr
  refine ⟨fun _ => 2, by simp, ?_⟩
  simp [gijswijtBlockWord, gijswijtBlock_one (m := 2) (by decide)]

-- Three copies already exceed the order-two curling bound.
example : ¬ ([2, 2, 2] <+: gijswijtBlock 2 2 ∧
    [2, 2, 2].length < (gijswijtBlock 2 2).length ∧ curlingNumber [2, 2, 2] ≤ 2) := by
  intro h
  exact (by decide : ¬ curlingNumber [2, 2, 2] ≤ 2) h.2.2
