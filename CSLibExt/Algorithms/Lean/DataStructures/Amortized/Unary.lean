/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# The unary (sequence) amortized framework

The `Amortized` locale of `Amortized_Framework0.thy`: operations act
on a single state type, in a sequence starting from `init`.
Superseded by the rose-tree framework in `Amortized.Framework`, but
still of interest because of its simplicity — and it is the form
closest to the book's presentation (Ch. 19: a sequence of
operations from an initial state, `Phi init = 0`). Main results:
`unary_aeq` (telescoping), `unary_TA`, `unary_aa1`, `unary_ub`.

Ported from the Chapter 22 Lean conversion in
`converted_proofs/ch22/lean/Chapter22.lean`, itself a conversion of the
Isabelle/HOL sources: the AFP entries `Skew_Heap` (`Skew_Heap.thy`) and
`Amortized_Complexity` (`Skew_Heap_Analysis.thy`,
`Amortized_Framework.thy`, `Priority_Queue_ops_merge.thy`), and
Tobias Nipkow (ed.), *Functional Data Structures and Algorithms: A Proof
Assistant Approach*, Chapter 22 (Skew Heaps, pp. 253-256) with Appendix
B.10. Isabelle-derived names are kept for traceability to those sources.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace Amortized

variable {Op State : Type u}

/- ## The unary (sequence) amortized framework (`Amortized_Framework0.thy`) -/

/-- The `Amortized` locale of `Amortized_Framework0.thy`: operations
act on a single state type, in a *sequence* starting from `init`.
Superseded by `AmortizedData` (which allows operations of arbitrary
arity and rose-tree histories), but still of interest because of its
simplicity — and it is the form closest to the book's presentation
(Ch. 19: a sequence of operations from an initial state, `Φ init = 0`).
Isabelle's `T` is real-valued here, as in that theory. -/
structure UnaryAmortized (Op State : Type u) where
  init : State
  nxt : Op → State → State
  inv : State → Prop
  T : Op → State → ℝ
  Phi : State → ℝ
  U : Op → State → ℝ
  inv_init : inv init
  inv_nxt : ∀ {f s}, inv s → inv (nxt f s)
  ppos : ∀ {s}, inv s → 0 ≤ Phi s
  p0 : Phi init = 0
  U_bound : ∀ {f s}, inv s → T f s + Phi (nxt f s) - Phi s ≤ U f s

/-- `state f n`: the state after performing the first `n` operations
of the sequence `f`. -/
def unaryState (A : UnaryAmortized Op State) (f : ℕ → Op) : ℕ → State
  | 0 => A.init
  | n + 1 => A.nxt (f n) (unaryState A f n)

/-- `A f i`: the amortized cost of the `i`-th operation. -/
def unaryA (A : UnaryAmortized Op State) (f : ℕ → Op) (i : ℕ) : ℝ :=
  A.T (f i) (unaryState A f i) + A.Phi (unaryState A f (i + 1)) -
    A.Phi (unaryState A f i)

/-- `inv_state`. -/
theorem unary_inv_state (A : UnaryAmortized Op State) (f : ℕ → Op) (n : ℕ) :
    A.inv (unaryState A f n) := by
  induction n with
  | zero => exact A.inv_init
  | succ n ih => exact A.inv_nxt ih

/-- `aeq`: telescoping, `∑ T = ∑ A - Φ (state n)`. -/
theorem unary_aeq (A : UnaryAmortized Op State) (f : ℕ → Op) (n : ℕ) :
    (∑ i ∈ Finset.range n, A.T (f i) (unaryState A f i)) =
      (∑ i ∈ Finset.range n, unaryA A f i) - A.Phi (unaryState A f n) := by
  induction n with
  | zero => simp [unaryA, unaryState, A.p0]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    simp only [unaryA]
    ring

/-- `TA`: total actual cost ≤ total amortized cost. -/
theorem unary_TA (A : UnaryAmortized Op State) (f : ℕ → Op) (n : ℕ) :
    (∑ i ∈ Finset.range n, A.T (f i) (unaryState A f i)) ≤
      (∑ i ∈ Finset.range n, unaryA A f i) := by
  rw [unary_aeq]
  have h := A.ppos (unary_inv_state A f n)
  linarith

/-- `aa1`: one operation's amortized cost is bounded by `U`. -/
theorem unary_aa1 (A : UnaryAmortized Op State) (f : ℕ → Op) (i : ℕ) :
    unaryA A f i ≤ A.U (f i) (unaryState A f i) :=
  A.U_bound (unary_inv_state A f i)

/-- `ub`: total actual cost ≤ total `U` bound. -/
theorem unary_ub (A : UnaryAmortized Op State) (f : ℕ → Op) (n : ℕ) :
    (∑ i ∈ Finset.range n, A.T (f i) (unaryState A f i)) ≤
      (∑ i ∈ Finset.range n, A.U (f i) (unaryState A f i)) :=
  le_trans (unary_TA A f n) (Finset.sum_le_sum fun i _ => unary_aa1 A f i)


end Amortized

end Cslib.Algorithms.Lean
