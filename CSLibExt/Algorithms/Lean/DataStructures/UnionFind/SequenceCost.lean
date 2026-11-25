/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.UnionFind.Rank
public import CSLibExt.Algorithms.Lean.DataStructures.UnionFind.Find
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Linarith

/-!
# Cost of operation sequences on union by rank with path compression

A cost model for sequences of make-set, find and union operations on the canonical Batteries
union-find (linking by rank, `find` with path compression), and the inverse Ackermann function
of Tarjan and van Leeuwen, *Worst-case analysis of set union algorithms*, J. ACM 31(2) (1984)
245–281, §1.

**Cost model** (Tarjan–van Leeuwen §1–3: the time of a find is proportional to the number of
nodes on its find path, make-set and link take constant time). A make-set costs `1`. A find on
`x` costs the number of nodes on the path from `x` to its root, `findPathLength uf x + 1`. A
union on `x, y` performs, as `Batteries.UnionFind.union` does, a find on `x`, then a find on `y`
in the compressed structure, then a link, and costs the two find costs plus `1`. An operation on
an index that is not allocated changes nothing and costs `1`. In the operation counts, a union
counts as two finds (`numFinds`), as in Tarjan–van Leeuwen §1.

**Results.** `run_cost_le_log` proves the bound `n + m (⌊log₂ n⌋ + 2)` for a sequence with `n`
make-sets and `m` finds, the explicit form of the `O(n + m log n)` bound of Tarjan–van Leeuwen
§2, Theorem 2, which compression does not worsen. The optimal bound `O(n + m α(m + n, n))` of
their Theorem 3 is recorded in `WantedExt` with the definitions below.
-/

open Batteries

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UnionByRank

/-- **Tarjan–van Leeuwen's Ackermann function.** For `i, j ≥ 1`, `A(1, j) = 2 ^ j`,
`A(i, 1) = A(i - 1, 2)` for `i ≥ 2`, and `A(i, j) = A(i - 1, A(i, j - 1))` for `i, j ≥ 2`
(Tarjan and van Leeuwen, *Worst-case analysis of set union algorithms*, J. ACM 31(2) (1984),
§1). The values with `i = 0` or `j = 0` are unused and set to `0`. This variant starts from
`A(1, j) = 2 ^ j` rather than `j + 1` as Mathlib's `ack` does; by their Remark 1 this changes the
inverse function only by an additive constant. -/
def ackermannTvL : ℕ → ℕ → ℕ
  | 0, _ => 0
  | 1, j => 2 ^ j
  | _ + 2, 0 => 0
  | i + 2, 1 => ackermannTvL (i + 1) 2
  | i + 2, j + 2 => ackermannTvL (i + 1) (ackermannTvL (i + 2) (j + 1))
termination_by i j => (i, j)

/-- **Inverse Ackermann function of Tarjan and van Leeuwen.**
`α(m, n) = min {i ≥ 1 | A(i, ⌊m / n⌋) > log₂ n}` (Tarjan and van Leeuwen, *Worst-case analysis
of set union algorithms*, J. ACM 31(2) (1984), §1). Since `A(i, j)` is an integer,
`A(i, j) > log₂ n` is equivalent to `A(i, j) > ⌊log₂ n⌋` for `n ≥ 1`, which is the form used here;
the minimum is written as an infimum of natural numbers. -/
noncomputable def inverseAckermannTvL (m n : ℕ) : ℕ :=
  sInf {i : ℕ | 1 ≤ i ∧ Nat.log 2 n < ackermannTvL i (m / n)}

/-- **Set-union operations.** Make-set (allocate a new singleton), find on an element, and
union of the classes of two elements (Tarjan and van Leeuwen, *Worst-case analysis of set union
algorithms*, J. ACM 31(2) (1984), §1). -/
inductive Op
  | makeSet
  | find (x : ℕ)
  | union (x y : ℕ)

theorem exists_iterate_parent_eq_rootD (uf : UnionFind) (x : ℕ) :
    ∃ d, uf.parent^[d] x = uf.rootD x := by
  by_cases hx : x < uf.size
  · obtain ⟨d, hd, _, _⟩ := UnionFind.exists_first_iterate_rootD uf ⟨x, hx⟩
    exact ⟨d, hd⟩
  · refine ⟨0, ?_⟩
    simp [UnionFind.rootD, hx]

/-- **Length of a find path.** The number of parent pointers followed from `x` to reach its
root, that is, the least `d` with `parent^[d] x = rootD x`; the find path has
`findPathLength uf x + 1` nodes. -/
def findPathLength (uf : UnionFind) (x : ℕ) : ℕ :=
  Nat.find (exists_iterate_parent_eq_rootD uf x)

/-- **One set-union operation with its cost.** The structure after the operation and its cost:
`1` for a make-set; the number of nodes on the find path for a find; the costs of the find on
`x`, of the find on `y` in the compressed structure, and `1` for the link, for a union; `1` for
an operation on an unallocated index, which changes nothing. -/
def step (uf : UnionFind) : Op → UnionFind × ℕ
  | .makeSet => (uf.push, 1)
  | .find x =>
      if h : x < uf.size then ((uf.find ⟨x, h⟩).1, findPathLength uf x + 1) else (uf, 1)
  | .union x y =>
      if h : x < uf.size ∧ y < uf.size then
        (uf.union ⟨x, h.1⟩ ⟨y, h.2⟩,
          (findPathLength uf x + 1) + (findPathLength (uf.find ⟨x, h.1⟩).1 y + 1) + 1)
      else (uf, 1)

/-- **A sequence of set-union operations with its total cost.** Runs the operations from left
to right and adds their costs (see `step`). -/
def run : List Op → UnionFind → UnionFind × ℕ
  | [], uf => (uf, 0)
  | op :: ops, uf => ((run ops (step uf op).1).1, (step uf op).2 + (run ops (step uf op).1).2)

/-- **Number of make-set operations** in a sequence. -/
def numMakeSet : List Op → ℕ
  | [] => 0
  | .makeSet :: ops => numMakeSet ops + 1
  | _ :: ops => numMakeSet ops

/-- **Number of finds** in a sequence, a union counting as two finds (Tarjan and van Leeuwen,
*Worst-case analysis of set union algorithms*, J. ACM 31(2) (1984), §1). -/
def numFinds : List Op → ℕ
  | [] => 0
  | .makeSet :: ops => numFinds ops
  | .find _ :: ops => numFinds ops + 1
  | .union _ _ :: ops => numFinds ops + 2

/-- **Find paths are short under union by rank.** In a union-find structure built by make-set,
find and union, every find path has at most `⌊log₂ n⌋` edges, `n` being the number of nodes. -/
theorem findPathLength_le_log {uf : UnionFind} (h : Reachable uf) (x : ℕ) :
    findPathLength uf x ≤ Nat.log 2 uf.size :=
  Nat.find_min' _ (iterate_parent_log h x)

private theorem step_reachable {uf : UnionFind} (h : Reachable uf) (op : Op) :
    Reachable (step uf op).1 := by
  cases op with
  | makeSet => exact .push h
  | find x =>
      simp only [step]
      split
      · exact .find _ h
      · exact h
  | union x y =>
      simp only [step]
      split
      · exact .union _ _ h
      · exact h

private theorem step_size (uf : UnionFind) (op : Op) :
    (step uf op).1.size + numMakeSet [] = uf.size + (numMakeSet [op]) := by
  cases op with
  | makeSet => simp [step, numMakeSet, size_push]
  | find x =>
      simp only [step, numMakeSet]
      split <;> simp
  | union x y =>
      simp only [step, numMakeSet]
      split <;> simp [size_union]

private theorem step_cost (uf : UnionFind) (h : Reachable uf) (op : Op) (L : ℕ)
    (hL : Nat.log 2 uf.size ≤ L) :
    (step uf op).2 ≤ numMakeSet [op] + numFinds [op] * (L + 2) := by
  cases op with
  | makeSet => simp [step, numMakeSet, numFinds]
  | find x =>
      simp only [step, numMakeSet, numFinds]
      split
      · have := findPathLength_le_log h x
        omega
      · omega
  | union x y =>
      simp only [step, numMakeSet, numFinds]
      split
      · rename_i hxy
        have h1 := findPathLength_le_log h x
        have h2 := findPathLength_le_log (Reachable.find ⟨x, hxy.1⟩ h) y
        rw [UnionFind.find_size] at h2
        omega
      · omega

/-- **Cost bound `O(n + m log n)` for union by rank with path compression.** Starting from any
union-find structure built by make-set, find and union, a sequence of operations with `n`
make-sets and `m` finds (a union counting as two finds) costs at most
`n + m (⌊log₂ N⌋ + 2)`, where `N` is the number of nodes at the end. From the empty structure
`N = n`, which is the explicit form of Tarjan and van Leeuwen, *Worst-case analysis of set union
algorithms*, J. ACM 31(2) (1984), §2, Theorem 2 (`O(n + m log n)` with linking by rank), here
with path compression as well. -/
theorem run_cost_le_log (ops : List Op) {uf : UnionFind} (h : Reachable uf) :
    (run ops uf).2 ≤
      numMakeSet ops + numFinds ops * (Nat.log 2 (uf.size + numMakeSet ops) + 2) := by
  induction ops generalizing uf with
  | nil => simp [run]
  | cons op ops ih =>
      have hs := step_size uf op
      have hstep := step_cost uf h op (Nat.log 2 (uf.size + numMakeSet (op :: ops)))
        (Nat.log_mono_right (by omega))
      have hrest := ih (step_reachable h op)
      have hnum : numMakeSet (op :: ops) = numMakeSet [op] + numMakeSet ops := by
        cases op <;> simp [numMakeSet]
        omega
      have hfin : numFinds (op :: ops) = numFinds [op] + numFinds ops := by
        cases op <;> simp [numFinds] <;> omega
      have hsize : (step uf op).1.size + numMakeSet ops = uf.size + numMakeSet (op :: ops) := by
        simp only [numMakeSet] at hs
        rw [hnum]
        omega
      rw [hsize] at hrest
      simp only [run]
      rw [hfin, add_mul]
      rw [hnum] at hrest hstep ⊢
      linarith

/-- **Cost bound `O(n + m log n)` from the empty structure.** A sequence of set-union
operations with `n` make-sets and `m` finds (a union counting as two finds), run from the empty
union-find structure, costs at most `n + m (⌊log₂ n⌋ + 2)` (Tarjan and van Leeuwen, *Worst-case
analysis of set union algorithms*, J. ACM 31(2) (1984), §2, Theorem 2). -/
theorem run_empty_cost_le_log (ops : List Op) :
    (run ops UnionFind.empty).2 ≤
      numMakeSet ops + numFinds ops * (Nat.log 2 (numMakeSet ops) + 2) := by
  have := run_cost_le_log ops Reachable.empty
  simpa [UnionFind.empty, UnionFind.mkEmpty, UnionFind.size] using this

end Cslib.Algorithms.Lean.UnionByRank
