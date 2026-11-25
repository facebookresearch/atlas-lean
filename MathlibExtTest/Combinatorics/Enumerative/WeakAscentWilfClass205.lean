/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.List.Sublists
import MathlibExt.Combinatorics.Enumerative.WeakAscentWilfClass205

namespace MetaMathlibExt.weakAscent_wilf_class205

private abbrev leftPatterns : Finset (List ℕ) := {[1, 0, 0], [1, 0, 2], [1, 2, 0], [2, 0, 1]}
private abbrev rightPatterns : Finset (List ℕ) := {[1, 0, 2], [1, 1, 0], [1, 2, 0], [2, 0, 1]}

private theorem mem_iff (w : List ℕ) (P : Finset (List ℕ)) (n : ℕ) :
    w ∈ weakAscentAvoiders P n ↔ w.length = n ∧ IsWeakAscentSeq w ∧
      ∀ p ∈ P, ∀ l ∈ w.sublistsLen p.length, ¬ ∀ i < p.length, ∀ j < p.length,
        (l.getD i 0 < l.getD j 0 ↔ p.getD i 0 < p.getD j 0) := by
  simp [weakAscentAvoiders, ContainsPattern, List.mem_sublistsLen, and_imp]

-- At length zero the common count includes the empty word.
example : (weakAscentAvoiders rightPatterns 0).ncard = 1 := by
  rw [← weakAscent_wilf_class205]
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

-- The two families first differ as sets at length four.
example : [0, 1, 1, 0] ∈ weakAscentAvoiders leftPatterns 4 ∧
    [0, 1, 1, 0] ∉ weakAscentAvoiders rightPatterns 4 ∧
    [0, 1, 0, 0] ∈ weakAscentAvoiders rightPatterns 4 ∧
    [0, 1, 0, 0] ∉ weakAscentAvoiders leftPatterns 4 := by
  have ha : IsWeakAscentSeq [0, 1, 1, 0] := by unfold IsWeakAscentSeq; decide
  have hb : IsWeakAscentSeq [0, 1, 0, 0] := by unfold IsWeakAscentSeq; decide
  simp only [mem_iff, ha, hb, true_and]
  decide

end MetaMathlibExt.weakAscent_wilf_class205
