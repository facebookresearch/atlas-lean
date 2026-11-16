/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD

/-!
# Catalan numbers by dynamic programming

Mathlib defines `catalan` by the recurrence
`catalan (n + 1) = ∑ i : Fin n.succ, catalan i * catalan (n - i)`, by well-founded
recursion, so `decide` and `rfl` do not evaluate it. `catalanTable n` evaluates the same
recurrence bottom up by structural recursion: it is the list of the first `n + 1` values, and
each new entry is computed from the entries already in the list. Its values reduce by
`decide`, and `catalanDP_eq_catalan` transfers them to `catalan` (see the tests).

## Main declarations

* `MetaMathlibExt.catalanTable`: the first `n + 1` values of the recurrence, as a list.
* `MetaMathlibExt.catalanDP`: the last entry of `catalanTable n`.
* `MetaMathlibExt.catalanDP_eq_catalan`: the table computes Mathlib's `catalan`.
-/

@[expose] public section

namespace MetaMathlibExt

/-- The first `n + 1` values of the Catalan recurrence, computed bottom up.
`catalanTable (n + 1)` appends to `catalanTable n` the entry
`∑ i ∈ Finset.range (n + 1), c i * c (n - i)`, where `c k` is entry `k` of `catalanTable n`.
The recurrence reads only indices at most `n`, below the length `n + 1`, so the default `0`
of `List.getD` is never read. -/
def catalanTable : ℕ → List ℕ
  | 0 => [1]
  | n + 1 =>
      let p := catalanTable n
      p ++ [∑ i ∈ Finset.range (n + 1), p.getD i 0 * p.getD (n - i) 0]

/-- The last entry of `catalanTable n`; it is `catalan n` (`catalanDP_eq_catalan`). -/
def catalanDP (n : ℕ) : ℕ := (catalanTable n).getD n 0

private theorem catalanTable_length (n : ℕ) : (catalanTable n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [catalanTable, ih]

private theorem catalanTable_succ (n : ℕ) :
    catalanTable (n + 1) = catalanTable n ++
      [∑ i ∈ Finset.range (n + 1),
        (catalanTable n).getD i 0 * (catalanTable n).getD (n - i) 0] :=
  rfl

private theorem catalanTable_getD_succ (n k : ℕ) (hk : k ≤ n) :
    (catalanTable (n + 1)).getD k 0 = (catalanTable n).getD k 0 := by
  have hlt : k < (catalanTable n).length := by rw [catalanTable_length]; omega
  rw [catalanTable_succ]
  exact List.getD_append _ _ _ _ hlt

private theorem catalanTable_getD (m k : ℕ) (h : k ≤ m) :
    (catalanTable m).getD k 0 = catalanDP k := by
  induction m generalizing k with
  | zero =>
    obtain rfl : k = 0 := by omega
    rfl
  | succ m ih =>
    by_cases hkm : k = m + 1
    · subst hkm
      rfl
    · rw [catalanTable_getD_succ m k (by omega), ih k (by omega)]

private theorem catalanDP_succ (n : ℕ) :
    catalanDP (n + 1) = ∑ i ∈ Finset.range (n + 1), catalanDP i * catalanDP (n - i) := by
  change (catalanTable (n + 1)).getD (n + 1) 0 = _
  rw [catalanTable_succ, List.getD_append_right _ _ _ _ (catalanTable_length n).le]
  simp only [catalanTable_length, Nat.sub_self, List.getD_cons_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [catalanTable_getD n i (by omega), catalanTable_getD n (n - i) (Nat.sub_le n i)]

private theorem catalan_succ_range (n : ℕ) :
    catalan (n + 1) = ∑ i ∈ Finset.range (n + 1), catalan i * catalan (n - i) := by
  rw [catalan_succ n, Fin.sum_univ_eq_sum_range (fun i => catalan i * catalan (n - i)) (n + 1)]

/-- The dynamic-programming table computes the Catalan numbers. -/
theorem catalanDP_eq_catalan (n : ℕ) : catalanDP n = catalan n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [catalanDP, catalanTable]
    | succ n =>
      rw [catalanDP_succ n, catalan_succ_range n]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [ih i hi, ih (n - i) (by omega)]

end MetaMathlibExt
