/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Four-Russians edit distance in subquadratic time

For strings of lengths `n ≥ m` over a finite alphabet with insertion,
deletion, and replacement costs that are integral multiples of a single
positive real, the Wagner-Fischer recurrence gives the edit distance
(`δ`, with the stated base cases). Precomputing every `m × m` block problem
— pairs of length-`m` substrings with input step vectors in range — answers
each block by table lookup, computing the distance in
`O(n * max(1, m / log n))` steps (`O(n^2 / log n)` for two length-`n`
strings) on a unit-cost RAM. The RAM time bound needs a concrete cost model
and is context here; the discreteness condition is necessary for the bound.

Overlap: none found (`CSLibExt/Algorithms/Lean/DynamicProgramming/EditDistance`
has the edit-distance metric and dynamic program; the block decomposition,
table-size bound, and subquadratic procedure are new).

Sources: W. J. Masek and M. S. Paterson, "A faster algorithm computing string
edit distances", Journal of Computer and System Sciences 20(1):18-31, 1980,
doi:10.1016/0022-0000(80)90002-1, Theorems 1-2 and Algorithm Y.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.MinMax
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.FourRussiansWanted

open Classical

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Sum of a real list. -/
def listSum : List ℝ → ℝ
  | [] => 0
  | v :: vs => v + listSum vs

/-- Edit costs: insert, delete, replace, all nonnegative. -/
structure EditCosts (α : Type*) where
  ins : α → ℝ
  del : α → ℝ
  rep : α → α → ℝ
  ins_nonneg : ∀ a, 0 ≤ ins a
  del_nonneg : ∀ a, 0 ≤ del a
  rep_nonneg : ∀ a b, 0 ≤ rep a b

/-- A pairwise script alignment: equal-length rows over `Option α`. -/
structure ScriptAlignment (α : Type*) where
  left : List (Option α)
  right : List (Option α)
  len_eq : left.length = right.length

/-- Script cost: inserts, deletes, and replacements column by column. -/
def scriptCost (c : EditCosts α) (A : ScriptAlignment α) : ℝ :=
  listSum ((A.left.zip A.right).map fun p => match p with
    | (none, some b) => c.ins b
    | (some a, none) => c.del a
    | (some a, some b) => c.rep a b
    | (none, none) => 0)

/-- Validity: rows erase to the two strings. -/
def IsScriptOf (A : ScriptAlignment α) (X Y : List α) : Prop :=
  A.left.filterMap id = X ∧ A.right.filterMap id = Y

/-- Edit distance: infimum of script costs. Characterized by `hδ_le`
(lower bound) and `hδ_att` (attainment) in the theorems below. -/
noncomputable def editDistance (c : EditCosts α) (X Y : List α) : ℝ :=
  sInf {v | ∃ A : ScriptAlignment α, IsScriptOf A X Y ∧
    scriptCost c A = v}

/-- A block problem: two length-`m` substrings with input step vectors. -/
structure BlockProblem (α : Type*) (m : ℕ) where
  top : List α
  leftStr : List α
  topLen : top.length = m
  leftLen : leftStr.length = m
  rowSteps : Fin m → ℤ
  colSteps : Fin m → ℤ

/-- Block match: same substrings and step vectors. -/
def BlockMatch {m : ℕ} (P E : BlockProblem α m) : Prop :=
  P.top = E.top ∧ P.leftStr = E.leftStr ∧
    P.rowSteps = E.rowSteps ∧ P.colSteps = E.colSteps

/-- In-range steps: every entry within `[-B, B]`. -/
def InRange {m : ℕ} (P : BlockProblem α m) (B : ℕ) : Prop :=
  (∀ i, P.rowSteps i ≤ B ∧ -(B : ℤ) ≤ P.rowSteps i) ∧
    ∀ i, P.colSteps i ≤ B ∧ -(B : ℤ) ≤ P.colSteps i

/-- **Wagner-Fischer base cases** (Masek-Paterson 1980, Theorem 1):
hypotheses are the costs `c`, strings `X`, `Y`, and the all-delete/all-insert
scripts (`Adel`, `Ains`) with correct erasure and stated costs (`hdel`,
`hins`). Conclusions: empty-empty distance is zero; first row/column are the
deletion/insertion sums.

Source: Masek-Paterson (1980), Theorem 1. -/
theorem_wanted wagnerFischer_base (c : EditCosts α)
    (X Y : List α)
    (Adel : ScriptAlignment α)
    (hdel : IsScriptOf Adel X [] ∧
      scriptCost c Adel = listSum (X.map c.del))
    (Ains : ScriptAlignment α)
    (hins : IsScriptOf Ains [] Y ∧
      scriptCost c Ains = listSum (Y.map c.ins)) :
    editDistance c [] [] = 0 ∧
      editDistance c X [] = scriptCost c Adel ∧
      editDistance c [] Y = scriptCost c Ains

/-- **Wagner-Fischer recurrence** (Masek-Paterson 1980, Theorem 2):
hypotheses are the costs, strings split at last letters `a`, `b`, and the
`editDistance` characterization (`hδ_le`, `hδ_att`). Conclusion: the
three-way minimum recurrence.

Source: Masek-Paterson (1980), Theorem 2. -/
theorem_wanted wagnerFischer_rec (c : EditCosts α)
    (X' Y' : List α) (a b : α)
    (hδ_le : ∀ (U V : List α) (A : ScriptAlignment α),
      IsScriptOf A U V → editDistance c U V ≤ scriptCost c A)
    (hδ_att : ∀ U V : List α, ∃ A : ScriptAlignment α,
      IsScriptOf A U V ∧ editDistance c U V = scriptCost c A) :
    editDistance c (X' ++ [a]) (Y' ++ [b]) =
      min (min (editDistance c X' Y' + c.rep a b)
        (editDistance c (X' ++ [a]) Y' + c.del a))
        (editDistance c X' (Y' ++ [b]) + c.ins b)

/-- **Four-Russians block correctness and table bound** (Masek-Paterson 1980,
Algorithm Y): hypotheses are a finite alphabet, integral costs (`hdiscrete`:
every cost is a natural multiple of one positive `c0`), block size `m`
(`hm`), a step range `B`, a table `entries` answering every in-range block
with the true distance (`htable`), and inputs `X`, `Y` with at least `m`
symbols each (`hXY`). Conclusions: the target block problem `P` is matched in
the table with the true distance value, and the table has at most
`|Σ|^(2m) * (2B+1)^(2m)` entries.

Source: Masek-Paterson (1980), Algorithm Y. -/
theorem_wanted fourRussians_correct (c : EditCosts α)
    (c0 : ℝ) (hc0 : 0 < c0)
    (hdiscrete : (∀ a, ∃ k : ℕ, c.ins a = k * c0) ∧
      (∀ a, ∃ k : ℕ, c.del a = k * c0) ∧
      ∀ a b, ∃ k : ℕ, c.rep a b = k * c0)
    (m : ℕ) (hm : 1 ≤ m)
    (B : ℕ)
    (entries : List (BlockProblem α m))
    (answers : BlockProblem α m → ℝ)
    (htable : ∀ P : BlockProblem α m, InRange P B →
      ∃ E ∈ entries, BlockMatch P E ∧ answers E = editDistance c E.top E.leftStr)
    (X Y : List α)
    (hX : (X.take m).length = m) (hY : (Y.take m).length = m)
    (P : BlockProblem α m)
    (hP : P.top = X.take m ∧ P.leftStr = Y.take m ∧ InRange P B) :
    (∃ E ∈ entries, BlockMatch P E ∧
      answers E = editDistance c X Y) ∧
      entries.length ≤ Fintype.card α ^ (2 * m) * (2 * B + 1) ^ (2 * m)

end WantedExt.Biology.ComputationalBiology.FourRussiansWanted

-- Note: `-(B : ℤ)` needs Neg Int (core) and OfNat (core): fine.
-- `(X.take m).length` needs no import: List.take/length core.
