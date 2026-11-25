/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.KSumMultisetDeterminesSetErdosProblem494
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open Finset
open MathlibExt.Combinatorics.KSumMultisetDeterminesSetErdosProblem494Wanted

-- The empty subset contributes one sum, including when the original set is empty.
example (A : Finset ℂ) : kSumMultiset A 0 = {0} := by
  simp [kSumMultiset]

-- Two different pairs, {0, 3} and {1, 2}, both contribute 3.
example :
    let e : ℕ ↪ ℂ := ⟨Nat.cast, Nat.cast_injective⟩
    kSumMultiset ((range 4).map e) 2 = {1, 2, 3, 3, 4, 5} := by
  intro e
  have pairs : (((range 4).powersetCard 2).val.map fun s => ∑ n ∈ s, n) =
      ({1, 2, 3, 3, 4, 5} : Multiset ℕ) := by decide
  have h := congrArg (Multiset.map e) pairs
  simp only [kSumMultiset, powersetCard_map, map_val, Multiset.map_map, Function.comp_apply]
  simpa [e, Function.comp_def, Multiset.map_map, Nat.cast_sum] using h

example (A : Finset ℂ) (k : ℕ) (hk : A.card < k) : kSumMultiset A k = 0 := by
  simp [kSumMultiset, powersetCard_eq_empty.mpr hk]
