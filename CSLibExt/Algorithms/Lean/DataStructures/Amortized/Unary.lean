/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`thys/Amortized_Complexity/Amortized_Framework0.thy` (Archive of Formal Proofs, entry `Amortized Complexity`, https://isa-afp.org/entries/Amortized_Complexity.html):
Copyright (c) 2014 Tobias Nipkow. All rights reserved.
Licensed under the BSD License.
Authors: Tobias Nipkow
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.PotentialMethod
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
operations from an initial state, `Phi init = 0`). The telescoping
results (`unary_aeq`, `unary_TA`, `unary_ub`) are specializations of
the generic potential-method API in `PotentialMethod`; the Isabelle
names are retained here as compatibility wrappers. `unary_aa1` is the
locale's own per-operation `U` bound.

Source: the AFP entry `Amortized Complexity` (Tobias Nipkow,
2014; BSD), `thys/Amortized_Complexity/Amortized_Framework0.thy`
(https://isa-afp.org/entries/Amortized_Complexity.html), the unary
`Amortized` locale. Book: Ch. 19, a sequence of operations from an
initial state. The structure and proofs are re-established in Lean;
Isabelle-derived names are kept for traceability.
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

/-- `A f i`: the amortized cost of the `i`-th operation. This is
`PotentialMethod.amortizedCost` specialized to the run `unaryState A f`
with actual costs `A.T (f i) (unaryState A f i)`; the Isabelle name is
retained as a compatibility wrapper. -/
def unaryA (A : UnaryAmortized Op State) (f : ℕ → Op) (i : ℕ) : ℝ :=
  PotentialMethod.amortizedCost A.Phi (unaryState A f)
    (fun i => A.T (f i) (unaryState A f i)) i

/-- `inv_state`. -/
theorem unary_inv_state (A : UnaryAmortized Op State) (f : ℕ → Op) (n : ℕ) :
    A.inv (unaryState A f n) := by
  induction n with
  | zero => exact A.inv_init
  | succ n ih => exact A.inv_nxt ih

/-- `aeq`: telescoping, `∑ T = ∑ A - Φ (state n)`.
Specialization of `PotentialMethod.sum_cost_eq` (the `Φ (state 0)` term
vanishes by `p0`). -/
theorem unary_aeq (A : UnaryAmortized Op State) (f : ℕ → Op) (n : ℕ) :
    (∑ i ∈ Finset.range n, A.T (f i) (unaryState A f i)) =
      (∑ i ∈ Finset.range n, unaryA A f i) - A.Phi (unaryState A f n) := by
  have h := PotentialMethod.sum_cost_eq A.Phi (unaryState A f)
    (fun i => A.T (f i) (unaryState A f i)) n
  have h0 : A.Phi (unaryState A f 0) = 0 := A.p0
  rw [h0, add_zero] at h
  calc (∑ i ∈ Finset.range n, A.T (f i) (unaryState A f i))
      = (∑ i ∈ Finset.range n, PotentialMethod.amortizedCost A.Phi (unaryState A f)
          (fun i => A.T (f i) (unaryState A f i)) i) - A.Phi (unaryState A f n) := h
    _ = (∑ i ∈ Finset.range n, unaryA A f i) - A.Phi (unaryState A f n) := by
        have hsum : (∑ i ∈ Finset.range n, PotentialMethod.amortizedCost A.Phi (unaryState A f)
            (fun i => A.T (f i) (unaryState A f i)) i) =
          (∑ i ∈ Finset.range n, unaryA A f i) :=
        Finset.sum_congr rfl (fun i _ => rfl)
        rw [hsum]

/-- `TA`: total actual cost ≤ total amortized cost.
Specialization of
`PotentialMethod.sum_cost_le_sum_amortizedCost_of_nonneg` (initial
potential zero by `p0`, potential nonnegative by `ppos`). -/
theorem unary_TA (A : UnaryAmortized Op State) (f : ℕ → Op) (n : ℕ) :
    (∑ i ∈ Finset.range n, A.T (f i) (unaryState A f i)) ≤
      (∑ i ∈ Finset.range n, unaryA A f i) := by
  have h := PotentialMethod.sum_cost_le_sum_amortizedCost_of_nonneg A.Phi
    (unaryState A f) (fun i => A.T (f i) (unaryState A f i))
    A.p0 (fun i => A.ppos (unary_inv_state A f i)) n
  have hsum : (∑ i ∈ Finset.range n,
      PotentialMethod.amortizedCost A.Phi (unaryState A f)
        (fun i => A.T (f i) (unaryState A f i)) i) =
      (∑ i ∈ Finset.range n, unaryA A f i) :=
    Finset.sum_congr rfl (fun i _ => rfl)
  rw [hsum] at h
  exact h

/-- `aa1`: one operation's amortized cost is bounded by `U`. -/
theorem unary_aa1 (A : UnaryAmortized Op State) (f : ℕ → Op) (i : ℕ) :
    unaryA A f i ≤ A.U (f i) (unaryState A f i) :=
  A.U_bound (unary_inv_state A f i)

/-- `ub`: total actual cost ≤ total `U` bound.
Specialization of `PotentialMethod.sum_cost_le_of_amortizedCost_le`
with per-operation bound `unary_aa1` (the final-potential term is
nonpositive by `ppos`). -/
theorem unary_ub (A : UnaryAmortized Op State) (f : ℕ → Op) (n : ℕ) :
    (∑ i ∈ Finset.range n, A.T (f i) (unaryState A f i)) ≤
      (∑ i ∈ Finset.range n, A.U (f i) (unaryState A f i)) := by
  have h := PotentialMethod.sum_cost_le_of_amortizedCost_le A.Phi (unaryState A f)
    (fun i => A.T (f i) (unaryState A f i))
    (fun i => A.U (f i) (unaryState A f i)) n
    (fun i _ => unary_aa1 A f i)
  have h0 : A.Phi (unaryState A f 0) = 0 := A.p0
  have hnn : 0 ≤ A.Phi (unaryState A f n) := A.ppos (unary_inv_state A f n)
  rw [h0, add_zero] at h
  exact le_trans h (sub_le_self _ hnn)


end Amortized

end Cslib.Algorithms.Lean
