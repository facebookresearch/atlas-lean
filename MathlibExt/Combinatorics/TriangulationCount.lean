/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Triangulation counts

Counts of triangulations of convex polygons by the
root-triangle recurrence. The count for an `(n + 2)`-gon
is the Catalan number. Polygon geometry is not included
here.
-/

@[expose] public section

/-- Triangulation counts by dynamic programming (ALG-46
core). `triList n` lists `triCount 0, ..., triCount n`,
where `triCount k` counts triangulations of a convex
`(k + 2)`-gon by the root-triangle decomposition: the
triangle on a fixed side splits the polygon into smaller
polygons, summed over the split point. `getD` with default
`0` is used only at indices below the length. -/
def triList : ℕ → List ℕ
  | 0 => [1]
  | n + 1 =>
      let p := triList n
      p ++ [∑ i ∈ Finset.range (n + 1), p.getD i 0 * p.getD (n - i) 0]

/-- The number of triangulations of a convex `(n + 2)`-gon. -/
def triCount (n : ℕ) : ℕ := (triList n).getD n 0

private theorem triList_length (n : ℕ) : (triList n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [triList, ih]

private theorem triList_getD_prefix (n k : ℕ) (hk : k ≤ n) :
    (triList (n + 1)).getD k 0 = (triList n).getD k 0 := by
  have hlt : k < (triList n).length := by rw [triList_length]; omega
  have hEq : triList (n + 1) =
      triList n ++ [∑ i ∈ Finset.range (n + 1), (triList n).getD i 0 * (triList n).getD (n - i) 0] := rfl
  rw [hEq]
  exact List.getD_append _ _ _ _ hlt

private theorem triList_getD_eq_triCount (m k : ℕ) (h : k ≤ m) :
    (triList m).getD k 0 = triCount k := by
  induction m generalizing k with
  | zero =>
    have hk : k = 0 := by omega
    subst hk
    rfl
  | succ m ih =>
    by_cases hkm : k = m + 1
    · subst hkm
      rfl
    · have hle : k ≤ m := by omega
      rw [triList_getD_prefix m k hle, ih k hle]

private theorem triCount_succ (n : ℕ) :
    triCount (n + 1) = ∑ i ∈ Finset.range (n + 1), triCount i * triCount (n - i) := by
  have hlen : (triList n).length = n + 1 := triList_length n
  have hEq : triList (n + 1) =
      triList n ++ [∑ i ∈ Finset.range (n + 1), (triList n).getD i 0 * (triList n).getD (n - i) 0] := rfl
  have hle : (triList n).length ≤ n + 1 := hlen.le
  show (triList (n + 1)).getD (n + 1) 0 = _
  rw [hEq, List.getD_append_right _ _ _ _ hle]
  simp only [hlen, Nat.sub_self]
  simp only [List.getD_cons_zero]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  have hi_le : i ≤ n := by omega
  have hni_le : n - i ≤ n := Nat.sub_le n i
  rw [triList_getD_eq_triCount n i hi_le, triList_getD_eq_triCount n (n - i) hni_le]

private theorem catalan_succ_range (n : ℕ) :
    catalan (n + 1) = ∑ i ∈ Finset.range (n + 1), catalan i * catalan (n - i) := by
  rw [catalan_succ n, Fin.sum_univ_eq_sum_range (fun i => catalan i * catalan (n - i)) (n + 1)]

/-- The triangulation count is the Catalan number. -/
theorem triCount_eq_catalan (n : ℕ) : triCount n = catalan n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [triCount, triList]
    | succ n =>
      rw [triCount_succ n, catalan_succ_range n]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_range] at hi
      have hni_lt : n - i < n + 1 := by omega
      rw [ih i hi, ih (n - i) hni_lt]

end
