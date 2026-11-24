/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.MultipleZeta.OOZDuality

open MetaMathlibExt

example : szDualIndex [2, 0, 1] = [1, 2, 0] := by decide

example : oozToSZ [3, 2] [2, 1] = 4 := by
  have h : Finset.Icc 1 3 = {1, 2, 3} := by decide
  norm_num [oozToSZ, oozToSZTail, h, Finset.sum_range_succ, Finsupp.mapDomain_add,
    Finsupp.single_apply, Nat.choose]

-- The preimage of the dual of [1, 0] under V has a negative coefficient.
example : oozQMZV [2] - oozQMZV [1] = oozQMZV [1, 0] := by
  let x : List ℕ →₀ ℚ := Finsupp.single [2] 1 - Finsupp.single [1] 1
  have hx : x ∈ Finsupp.supported ℚ ℚ {v : List ℕ | ∀ a ∈ v.head?, 1 ≤ a} := by
    apply Submodule.sub_mem
    · exact Finsupp.single_mem_supported ℚ _ (by simp)
    · exact Finsupp.single_mem_supported ℚ _ (by simp)
  have hV : Finsupp.linearCombination ℚ oozToSZ x = (oozToSZ [1, 0]).mapDomain szDualIndex := by
    have h : Finset.Icc 1 2 = {1, 2} := by decide
    simp [x, oozToSZ, oozToSZTail, h, Nat.choose, szDualIndex, szWord, szIndexOfWordAux]
  have h := sum_oozQMZV_eq_of_oozToSZ_eq_szDual [1, 0] (by simp) x hx hV
  change Finsupp.linearCombination ℚ oozQMZV x = _ at h
  simpa [x] using h
