/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.List.Sublists
import MathlibExt.Combinatorics.Enumerative.WeakAscentWilfClass162

namespace MetaMathlibExt.weakAscent_wilf_class162

private abbrev leftPatterns : Finset (List ℕ) := {[0, 1, 0], [1, 0, 0], [1, 0, 1], [1, 2, 0]}
private abbrev rightPatterns : Finset (List ℕ) := {[0, 1, 0], [1, 0, 0], [1, 1, 0], [1, 2, 0]}

private theorem mem_iff (w : List ℕ) (P : Finset (List ℕ)) (n : ℕ) :
    w ∈ weakAscentAvoiders P n ↔ w.length = n ∧ IsWeakAscentSeq w ∧
      ∀ p ∈ P, ∀ l ∈ w.sublistsLen p.length, ¬ ∀ i < p.length, ∀ j < p.length,
        (l.getD i 0 < l.getD j 0 ↔ p.getD i 0 < p.getD j 0) := by
  simp [weakAscentAvoiders, ContainsPattern, List.mem_sublistsLen, and_imp]

-- At length zero the common count includes the empty word.
example : (weakAscentAvoiders rightPatterns 0).ncard = 1 := by
  rw [← weakAscent_wilf_class162]
  have h : weakAscentAvoiders leftPatterns 0 = {[]} := by
    ext w
    constructor
    · intro hw
      exact List.length_eq_zero_iff.mp hw.1
    · rintro (rfl : w = [])
      rw [mem_iff]
      unfold IsWeakAscentSeq
      decide
  simp [h]

-- Moving the second maximum across the final one exchanges these length-five avoiders.
example : [0, 0, 2, 2, 1] ∈ weakAscentAvoiders leftPatterns 5 ∧
    [0, 0, 2, 2, 1] ∉ weakAscentAvoiders rightPatterns 5 ∧
    [0, 0, 2, 1, 2] ∈ weakAscentAvoiders rightPatterns 5 ∧
    [0, 0, 2, 1, 2] ∉ weakAscentAvoiders leftPatterns 5 := by
  have ha : IsWeakAscentSeq [0, 0, 2, 2, 1] := by unfold IsWeakAscentSeq; decide
  have hb : IsWeakAscentSeq [0, 0, 2, 1, 2] := by unfold IsWeakAscentSeq; decide
  simp only [mem_iff, ha, hb, true_and]
  decide

end MetaMathlibExt.weakAscent_wilf_class162
