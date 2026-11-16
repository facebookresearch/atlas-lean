/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic

import Mathlib.Algebra.BigOperators.Fin

/-!
# Catalan numbers by dynamic programming

Mathlib defines `catalan` by the recurrence
`catalan (n + 1) = ∑ i : Fin n.succ, catalan i * catalan (n - i)`, by well-founded
recursion, so `decide` and `rfl` do not evaluate it. `catalanTable n` evaluates the same
recurrence bottom up by structural recursion: it is the list of the first `n + 1` values, and
each new entry is the sum of the pointwise products of the list and its reverse, computed in
linear time. Its values reduce by `decide`, and `catalanDP_eq_catalan` transfers them to
`catalan` (see the tests).

## Main declarations

* `MetaMathlibExt.catalanTable`: the first `n + 1` values of the recurrence, as a list.
* `MetaMathlibExt.catalanTable_eq_map_range`: `catalanTable n` lists `catalan 0, …, catalan n`.
* `MetaMathlibExt.catalanDP`: the last entry of `catalanTable n`.
* `MetaMathlibExt.catalanDP_eq_catalan`: the table computes Mathlib's `catalan`.
-/

@[expose] public section

namespace MetaMathlibExt

/-- The first `n + 1` values of the Catalan recurrence, computed bottom up.
`catalanTable (n + 1)` appends to `p = catalanTable n` the entry
`∑ i, p[i] * p[n - i]`, computed as the sum of the pointwise products of `p` and its reverse
(`List.zipWith`), so each new entry takes time linear in the length of `p`. -/
def catalanTable : ℕ → List ℕ
  | 0 => [1]
  | n + 1 =>
      let p := catalanTable n
      p ++ [(List.zipWith (· * ·) p p.reverse).sum]

/-- The last entry of `catalanTable n`; it is `catalan n` (`catalanDP_eq_catalan`). -/
def catalanDP (n : ℕ) : ℕ := (catalanTable n).getD n 0

private theorem sum_range_eq_list_sum (m : ℕ) (g : ℕ → ℕ) :
    ∑ i ∈ Finset.range m, g i = ((List.range m).map g).sum := by
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range, Multiset.map_coe,
    Multiset.sum_coe]

private theorem reverse_range_succ (n : ℕ) :
    (List.range (n + 1)).reverse = (List.range (n + 1)).map (n - ·) := by
  nth_rewrite 1 [List.range_eq_range']
  rw [List.reverse_range']
  simp

/-- `catalanTable n` is the list `catalan 0, …, catalan n`. -/
theorem catalanTable_eq_map_range (n : ℕ) :
    catalanTable n = (List.range (n + 1)).map catalan := by
  induction n with
  | zero => simp [catalanTable]
  | succ n ih =>
    have hconv : (List.zipWith (· * ·) ((List.range (n + 1)).map catalan)
        ((List.range (n + 1)).map catalan).reverse).sum = catalan (n + 1) := by
      rw [← List.map_reverse, reverse_range_succ, List.map_map, List.zipWith_map,
        List.zipWith_self, ← sum_range_eq_list_sum, catalan_succ,
        Fin.sum_univ_eq_sum_range (fun i => catalan i * catalan (n - i))]
      rfl
    change catalanTable n ++ [_] = _
    rw [ih, hconv, List.range_succ (n := n + 1), List.map_append, List.map_singleton]

/-- The dynamic-programming table computes the Catalan numbers. -/
theorem catalanDP_eq_catalan (n : ℕ) : catalanDP n = catalan n := by
  simp [catalanDP, catalanTable_eq_map_range]

end MetaMathlibExt
