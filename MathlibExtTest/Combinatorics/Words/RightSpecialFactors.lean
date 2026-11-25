/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Words.RightSpecialFactors

open MetaMathlibExt

-- The constant word has no branching, so its factor complexity stays constant.
example (n : ℕ) (hn : 1 ≤ n) :
    wordFactorComplexity (fun _ => false) (n + 1) =
      wordFactorComplexity (fun _ => false) n := by
  simpa only [rightSpecialFactors_const_false, Set.ncard_empty, Nat.add_zero] using
    wordFactorComplexity_succ_eq_add_rightSpecial (fun _ => false) n (hn := hn)

-- In 01000⋯, the factor 0 has both right extensions, so complexity increases at length one.
example :
    wordFactorComplexity (fun i => decide (i = 1)) 1 <
      wordFactorComplexity (fun i => decide (i = 1)) 2 := by
  let a : ℕ → Bool := fun i => decide (i = 1)
  change wordFactorComplexity a 1 < wordFactorComplexity a (1 + 1)
  rw [wordFactorComplexity_succ_eq_add_rightSpecial a 1 (hn := le_rfl)]
  apply Nat.lt_add_of_pos_right
  apply (Set.ncard_pos (Set.toFinite _)).mpr
  refine ⟨fun _ => false, ?_⟩
  intro b
  cases b
  · exact ⟨2, by decide⟩
  · exact ⟨0, by decide⟩
