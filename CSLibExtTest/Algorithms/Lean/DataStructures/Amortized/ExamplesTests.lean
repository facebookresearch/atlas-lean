/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.Amortized.Examples
public import CSLibExt.Algorithms.Lean.DataStructures.Amortized.ExamplesTablesQueues

/-!
# Amortized examples regression tests

Concrete reductions and bound checks for each framework example
instance: the binary counter (including a two-step rose-tree history
and the telescoping identity on it), multipop, the two dynamic-table
analyses, and the three queues. Costs count only the stated units.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Amortized.ExamplesTests

open Amortized

-- Binary counter: increment flips trailing ones and the next bit.
example : binCounterIncr [true, false, true] = [false, true, true] := rfl

-- Binary counter: the amortized cost of `incr` is exactly 2.
example :
    (binCounterTIncr [true, false, true] : ℝ) +
      binCounterPhi (binCounterIncr [true, false, true]) -
      binCounterPhi [true, false, true] = 2 :=
  binCounter_a_incr _

-- Binary counter: two-step history `empty` then `incr`; total cost 2.
example : cost_sum binCounterAmortized (.T .incr [.T .empty []]) = 2 := by
  norm_num [cost_sum, state, binCounterAmortized, binCounterExec, binCounterCost,
    binCounterTIncr]

-- Binary counter: telescoping on that history.
example :
    cost_sum binCounterAmortized (.T .incr [.T .empty []]) =
      acost_sum binCounterAmortized (.T .incr [.T .empty []]) -
        binCounterAmortized.Phi
          (state binCounterAmortized (.T .incr [.T .empty []])) :=
  t_sum_a_sum (A := binCounterAmortized)
    (by simp [wf, binCounterAmortized, binCounterArity])

-- Multipop: popping a singleton stack costs 1 and drops potential 1.
example :
    (multipopCost (.pop 1) [[5]] : ℝ) +
      multipopPhi (multipopExec (.pop 1) [[5]]) -
      multipopPhi [5] ≤ multipopU (.pop 1) [[5]] := by
  norm_num [multipopCost, multipopExec, multipopPhi, multipopU]

-- Dynamic table, insert only: `ins` on the empty table.
example :
    (dynTab1Cost .ins [(0, 0)] : ℝ) + dynTab1Phi (dynTab1Exec .ins [(0, 0)]) -
      dynTab1Phi (0, 0) ≤ dynTab1U .ins [(0, 0)] := by
  norm_num [dynTab1Cost, dynTab1Exec, dynTab1Phi, dynTab1U]

-- Dynamic table, insert and delete: `ins` and `del` on small tables.
example :
    (dynTab3Cost .ins [(0, 0)] : ℝ) + dynTab3Phi (dynTab3Exec .ins [(0, 0)]) -
      dynTab3Phi (0, 0) ≤ dynTab3U .ins [(0, 0)] := by
  norm_num [dynTab3Cost, dynTab3Exec, dynTab3Phi, dynTab3U]

example :
    (dynTab3Cost .del [(2, 2)] : ℝ) + dynTab3Phi (dynTab3Exec .del [(2, 2)]) -
      dynTab3Phi (2, 2) ≤ dynTab3U .del [(2, 2)] := by
  norm_num [dynTab3Cost, dynTab3Exec, dynTab3Phi, dynTab3U]

-- Queue with `adjust`: enqueue into `([1], [2])`.
example :
    (queue2Cost (.enq 5) [([1], [2])] : ℝ) +
      queue2Phi (queue2Exec (.enq 5) [([1], [2])]) =
      queue2Phi ([1], [2]) + 2 :=
  queue2Enq_sum 5 [1] [2]

-- Queue with `balance`: enqueue into `([1], [2])` within the `+ 3` bound.
example :
    (queue3Cost (.enq 5) [([1], [2])] : ℝ) +
      queue3Phi (queue3Exec (.enq 5) [([1], [2])]) ≤
      queue3Phi ([1], [2]) + 3 :=
  queue3Enq_bound 5 [1] [2]

-- Dynamic tables, generalised growth factor: the ceiling `⌈2 * 5⌉ = 10`.
example : Int.ceil ((2 : ℝ) * ((5 : ℕ) : ℝ)) = (10 : ℤ) := by
  rw [Int.ceil_eq_iff]
  norm_num

-- Dynamic tables, generalised growth factor: resizing from `(5, 5)`
-- with `c = 2` doubles the size to `⌈2 * 5⌉₊ = 10`, and the amortized
-- bound holds with equality (`6 + 2 - 5 = 3 ≤ 3`).
example :
    (dynTab2Cost .ins [(5, 5)] : ℝ) +
      dynTab2Phi 2 2 (dynTab2Exec 2 .ins [(5, 5)]) -
      dynTab2Phi 2 2 (5, 5) ≤ dynTab2U 2 2 .ins [(5, 5)] := by
  rw [dynTab2Cost_ins, dynTab2Exec_ins, dynTab2U_ins]
  have hins : dynTab2Ins 2 (5, 5) = (6, 10) := by
    simp only [dynTab2Ins]
    rw [ite_eq_right (by norm_num : ¬(5 : ℕ) < 5), ite_eq_right (by norm_num : ¬(5 : ℕ) = 0)]
    have hceil : Int.ceil ((2 : ℝ) * ((5 : ℕ) : ℝ)) = (10 : ℤ) := by
      rw [Int.ceil_eq_iff]
      norm_num
    rw [hceil]
    rfl
  rw [hins, ite_eq_right (by norm_num : ¬(5 : ℕ) < 5)]
  simp only [dynTab2Phi]
  norm_num

-- Queue: `deq` on an empty front list reverses the rear list.
example : queueExec .deq [([1, 2], ([] : List ℕ))] = ([], [1]) := by
  simp [queueExec]

-- Queue: the reversal case of the amortized bound (`2 + 0 - 2 ≤ 0`).
example :
    (queueCost .deq [([1, 2], ([] : List ℕ))] : ℝ) +
      queuePhi (queueExec .deq [([1, 2], ([] : List ℕ))]) -
      queuePhi ([1, 2], ([] : List ℕ)) ≤ queueU .deq [([1, 2], ([] : List ℕ))] := by
  rw [show queueExec .deq [([1, 2], ([] : List ℕ))] = ([], [1]) by simp [queueExec],
    queueCost_deq, queueU_deq]
  norm_num [queuePhi]

end Cslib.Algorithms.Lean.Amortized.ExamplesTests
