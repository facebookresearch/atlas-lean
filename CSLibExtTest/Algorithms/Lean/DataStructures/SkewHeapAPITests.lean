/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.SkewHeap
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Skew-heap public proof-interface tests

Clients of the skew-heap API can use the ADT instance, the merge
correctness lemmas, the full statements of Lemma 22.1 and the
logarithmic amortized bounds, Exercise 22.1, and the framework
specialisation — not merely selected projections. No total-runtime
claim is inferred from the `T_merge` / potential bounds.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.SkewHeapAPITests

open SkewHeap
open Amortized

variable {α : Type u} [LinearOrder α]

-- The ADT `Priority_Queue_Merge` instance is available as a value.
example : PriorityQueueMerge (SkewHeap.Tree ℕ) ℕ := skewPQMerge

-- The `Priority_Queue` instance is its first component.
example : PriorityQueue (SkewHeap.Tree ℕ) ℕ := skewPQMerge.toPQ

-- Check the complete merge-correctness statements.
example {t1 t2 : SkewHeap.Tree α} (h1 : heap t1) (h2 : heap t2) :
    heap (merge t1 t2) :=
  heap_merge h1 h2

example {t1 t2 : SkewHeap.Tree α} :
    toMultiset (merge t1 t2) = toMultiset t1 + toMultiset t2 :=
  mset_merge _ _

example {t1 t2 : SkewHeap.Tree α} :
    toSet (merge t1 t2) = toSet t1 ∪ toSet t2 :=
  set_merge _ _

example {t1 t2 : SkewHeap.Tree α} :
    size (merge t1 t2) = size t1 + size t2 :=
  size_merge _ _

-- Check the complete Lemma 22.1 statement.
example {t1 t2 : SkewHeap.Tree α} :
    (T_merge t1 t2 : ℤ) + Phi (merge t1 t2) - Phi t1 - Phi t2 ≤
      (lrh (merge t1 t2) : ℤ) + (rlh t1 : ℤ) + (rlh t2 : ℤ) + 1 :=
  amor_le _ _

-- Check the complete logarithmic amortized bounds.
example {t1 t2 : SkewHeap.Tree α} :
    (T_merge t1 t2 : ℝ) + (Phi (merge t1 t2) : ℝ) - (Phi t1 : ℝ) - (Phi t2 : ℝ) ≤
      3 * Real.logb 2 (size1 t1 + size1 t2) + 1 :=
  a_merge _ _

example {a : α} {t : SkewHeap.Tree α} :
    (T_insert a t : ℝ) + (Phi (insert a t) : ℝ) - (Phi t : ℝ) ≤
      3 * Real.logb 2 (size1 t + 2) + 1 :=
  a_insert _ _

example {t : SkewHeap.Tree α} :
    (T_delMin t : ℝ) + (Phi (delMin t) : ℝ) - (Phi t : ℝ) ≤
      3 * Real.logb 2 (size1 t + 2) + 1 :=
  a_delMin _

-- Check Exercise 22.1 in full generality: exactly `k` insertions.
example (k : ℕ) :
    ∃ ns : List ℕ,
      ns.length = k ∧
        height (List.foldl (fun t a => insert a t) SkewHeap.Tree.leaf ns) = k :=
  exercise_22_1 k

-- Check the framework specialisation: total cost is bounded by total `U`.
example {ot : RoseTree (PQOp α)} (hw : wf skewAmortized ot) :
    cost_sum skewAmortized ot ≤ U_sum skewAmortized ot :=
  skew_t_sum_le_U_sum hw

-- The `Heap_Merge` interpretation is available as a value.
example : HeapMerge α := skewHeapMerge

end Cslib.Algorithms.Lean.SkewHeapAPITests
