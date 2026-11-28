/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.CSP.BacktrackingEnum
public import Mathlib.Data.Fin.VecNotation

/-!
# Enumeration by backtracking with forward checking: tests

Kernel-checked fixtures (`decide`) on the `n`-queens problem as Haralick and Elliott (1980,
Section 3) set it up: variable `i` is the row of a queen and its value the column, every ordered
pair of distinct rows carries the constraint "different columns and different diagonals", the
domains are all columns, and the variable order is the natural one (`SearchOrder.ofLinearOrder`).

* Four queens: the enumeration is exactly `[![1, 3, 0, 2], ![2, 0, 3, 1]]`, `backtrackFC` returns
  its head, and the solution finset has 2 elements, both through `length_enumerateFC` and by brute
  force over all 256 assignments (OEIS A000170).
* Two and three queens have no solution, one queen has one, five queens have ten.
* Minimum remaining values lists the same two solutions for four queens.

Closed checks instantiate the theorems for an arbitrary problem and search order.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.CSPBacktracking

open Cslib.Algorithms.Lean.ArcConsistency

/-- `n` queens, one per row: variable `i` is the column of the queen in row `i`, and every ordered
pair of distinct rows `(i, j)` allows columns `a` and `b` when they differ and the two queens share
no diagonal. -/
def queens (n : ℕ) : BinaryCSP (Fin n) (Fin n) :=
  ⟨(List.finRange n).flatMap fun i => (List.finRange n).filterMap fun j =>
      if i = j then none else some (i, j),
    fun i j a b => a ≠ b ∧ (a : ℕ) + j ≠ b + i ∧ (a : ℕ) + i ≠ b + j⟩

example : enumerateFC (queens 4) SearchOrder.ofLinearOrder (fun _ => Finset.univ) =
    [![1, 3, 0, 2], ![2, 0, 3, 1]] := by decide

example : backtrackFC (queens 4) SearchOrder.ofLinearOrder (fun _ => Finset.univ) =
    some ![1, 3, 0, 2] := by decide

example : (solutionFinset (queens 4) (fun _ => Finset.univ)).card = 2 := by
  rw [← length_enumerateFC _ SearchOrder.ofLinearOrder SearchOrder.nodup_vals_ofLinearOrder]
  decide

set_option maxRecDepth 4000 in
/-- Brute force over all assignments, independent of the search. -/
example : solutionFinset (queens 4) (fun _ => Finset.univ) = {![1, 3, 0, 2], ![2, 0, 3, 1]} := by
  decide

example : IsSolution (queens 4) (fun _ => Finset.univ) ![2, 0, 3, 1] :=
  (mem_enumerateFC _ SearchOrder.ofLinearOrder).1 (by decide)

example : enumerateFC (queens 3) SearchOrder.ofLinearOrder (fun _ => Finset.univ) = [] := by decide

example : enumerateFC (queens 2) SearchOrder.ofLinearOrder (fun _ => Finset.univ) = [] := by decide

example : enumerateFC (queens 1) SearchOrder.ofLinearOrder (fun _ => Finset.univ) = [![0]] := by
  decide

example : (enumerateFC (queens 5) SearchOrder.ofLinearOrder (fun _ => Finset.univ)).length = 10 := by
  decide

example : enumerateFC (queens 4) SearchOrder.mrv (fun _ => Finset.univ) =
    [![1, 3, 0, 2], ![2, 0, 3, 1]] := by decide

/-! ## Closed checks -/

example {X D : Type*} [DecidableEq X] [Fintype X] [DecidableEq D] (P : BinaryCSP X D)
    (O : SearchOrder X D) (dom : X → Finset D) :
    (enumerateFC P O dom).toFinset = solutionFinset P dom :=
  toFinset_enumerateFC P O dom

example {X D : Type*} [DecidableEq X] [Fintype X] (P : BinaryCSP X D) (O : SearchOrder X D)
    (dom : X → Finset D) : backtrackFC P O dom = (enumerateFC P O dom).head? :=
  backtrackFC_eq_head?_enumerateFC P O dom

#print axioms toFinset_enumerateFC
#print axioms mem_enumerateFC
#print axioms nodup_enumerateFC
#print axioms length_enumerateFC
#print axioms backtrackFC_eq_head?_enumerateFC

end Cslib.Algorithms.Lean.CSPBacktracking
