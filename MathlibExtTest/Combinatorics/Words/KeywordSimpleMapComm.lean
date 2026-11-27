/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import MathlibExt.Combinatorics.Words.KeywordSimpleMapComm

namespace MetaMathlibExt.keywordSimpleMap_comm_iff

private abbrev keyword := ![false, false, false, true]

-- For the keyword 0001, the simple maps one letter apart commute: the prefix 000 is neither the
-- suffix 001 nor its negation 110.
example : keywordSimpleMap (n := 8) keyword 0 ∘ keywordSimpleMap keyword 1 =
    keywordSimpleMap keyword 1 ∘ keywordSimpleMap keyword 0 :=
  (keywordSimpleMap_comm_iff keyword 0 1 (by decide) (by decide)).mpr (Or.inl (by decide))

-- Three letters apart they do not commute: the prefix 0 is the negation of the suffix 1.
example : keywordSimpleMap (n := 8) keyword 0 ∘ keywordSimpleMap keyword 3 ≠
    keywordSimpleMap keyword 3 ∘ keywordSimpleMap keyword 0 := by
  rw [Ne, keywordSimpleMap_comm_iff keyword 0 3 (by decide) (by decide)]
  decide

-- Simple maps with disjoint windows commute.
example : keywordSimpleMap (n := 8) keyword 0 ∘ keywordSimpleMap keyword 4 =
    keywordSimpleMap keyword 4 ∘ keywordSimpleMap keyword 0 :=
  (keywordSimpleMap_comm_iff keyword 0 4 (by decide) (by decide)).mpr (Or.inr (by decide))

-- For a keyword of length one, any two simple maps commute.
example (a : Fin 1 → Bool) (i j n : ℕ) (hij : i < j) (hj : j < n) :
    keywordSimpleMap (n := n) a i ∘ keywordSimpleMap a j =
      keywordSimpleMap a j ∘ keywordSimpleMap a i :=
  (keywordSimpleMap_comm_iff a i j hij hj).mpr (Or.inr (by omega))

-- Simple maps exactly `m ≥ 1` letters apart never commute: the first letter of the keyword equals
-- its last letter or the negation of it.
example {m n : ℕ} (a : Fin (m + 1) → Bool) (i : ℕ) (hm : 1 ≤ m) (hn : i + 2 * m < n) :
    keywordSimpleMap (n := n) a i ∘ keywordSimpleMap a (i + m) ≠
      keywordSimpleMap a (i + m) ∘ keywordSimpleMap a i := by
  have hfirst : (List.ofFn a).take (m + 1 - (i + m - i)) = [a 0] := by
    rw [show m + 1 - (i + m - i) = 1 by omega, List.ofFn_succ]
    rfl
  have hlast : (List.ofFn a).drop (i + m - i) = [a (Fin.last m)] := by
    rw [List.ofFn_succ', List.concat_eq_append, List.drop_left' (by simp)]
  rw [Ne, keywordSimpleMap_comm_iff a i (i + m) (by omega) (by omega), hfirst, hlast]
  cases a 0 <;> cases a (Fin.last m) <;> simp

end MetaMathlibExt.keywordSimpleMap_comm_iff
