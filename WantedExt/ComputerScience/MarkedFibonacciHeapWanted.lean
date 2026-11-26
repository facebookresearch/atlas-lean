/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Algorithms.Lean.DataStructures.FibonacciHeap.Marked
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.Real.GoldenRatio

/-!
# Rank and amortized work of marked Fibonacci heaps

The inputs below are histories of pointer-level transitions, not forests satisfying a postulated
Fibonacci rank invariant. Four units of work per potential credit pay both the root visit and
rank-bin processing in a long consolidation (and more than cover a cascade step).
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.MarkedFibonacci

universe u

/-- **Rank bound and amortized costs of marked Fibonacci heaps.** Starting from empty, for every
live node of rank `k`, its current children, indexed from zero in link order, have rank at least
`i - 1` at index `i`. Its subtree contains at least the `(k + 2)`-nd Fibonacci number of distinct
live nodes, at least the golden ratio to the power `k`. Thus `k` is at most the base-golden-ratio
logarithm of the live size. With four units per root-plus-twice-marks credit, insertion, meld,
cached minimum lookup and decrease-key have bounded amortized work; extraction from size `s`
costs at most a constant times `1 + floor(log₂ s)` amortized. There is one uniform constant for
all legal histories: actual work for `m` operations with `n` insertions is at most that constant
times `m + n * floor(log₂ n)`, with binary logarithm zero at zero. Core histories are the
insert/extract-min/decrease-key theorem of Wayne, slide 3; extended histories also allow queries
and consume both disjoint inputs to every meld (slide 72). These bounds concern the handle
primitives, not the evaluation of a persistent forest. -/
theorem_wanted rank_and_amortized_costs :
    ∃ C : Nat, ∀ {α : Type u} [LinearOrder α] {e : Bool} {h : Heap α} {m n w : Nat},
      History e h m n w →
      (∀ x ∈ h.live,
        (∀ (i : Nat) (hi : i < (h.children x).length),
          i ≤ h.rank (h.children x)[i] + 1) ∧
        (∃ t : FibonacciTree Nat, h.View t ∧ t.root = x ∧ t.elements.Nodup ∧
          (∀ y ∈ t.elements, y ∈ h.live) ∧ Nat.fib (h.rank x + 2) ≤ t.elements.card) ∧
        Real.goldenRatio ^ h.rank x ≤ (Nat.fib (h.rank x + 2) : ℝ) ∧
        (h.rank x : ℝ) ≤ Real.logb Real.goldenRatio h.live.card) ∧
      (∀ {op : Op α} {h' : Heap α} {c : Nat}, Step h op h' c →
        c + 4 * h'.potential ≤ 4 * h.potential + C * op.allowance h.live.card) ∧
      (∀ {g : Heap α} {e' : Bool} {m' n' w' : Nat}, History e' g m' n' w' →
        Disjoint h.live g.live → 2 + 4 * (h.meld g).potential ≤
          4 * (h.potential + g.potential) + C) ∧
      w ≤ C * (m + n * n.log2)

end Cslib.Algorithms.Lean.MarkedFibonacci
