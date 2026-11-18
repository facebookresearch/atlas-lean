/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Graph.ArcNetwork
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Oriented branch ports and network power balance

## i. Overview

For a finite set of nodes and a finite set of distinct branch
identifiers, each branch has a tail node and a head node. The signed
graph incidence `MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix`
records `+1` at the head and `-1` at the tail. The electrical
incidence defined here is its negation, so the tail is positive and
the head is negative, and a branch voltage defined from node
potentials is the tail potential minus the head potential. Node
injections are supplied independently of branch currents. Current
balance at the nodes and the potential definition of branch voltage
together imply that total branch power equals total node power
(Tellegen's theorem). Reversing one branch, together with its
voltage and its current, leaves the node equations and the power
balance unchanged. Distinct branch identifiers that join the same
pair of nodes keep distinct columns as functions of the identifier,
and a branch whose tail and head coincide has a zero column.

## ii. Key results

- `branchPower_eq_nodePower`: Tellegen's identity in sum form,
  `∑ e, v e * i e = ∑ n, phi n * j n` from KVL and KCL.
- `branchPower_eq_nodePower_dotProduct`: the same identity in
  dot-product form, `v ⬝ᵥ i = phi ⬝ᵥ j`.
- `orientedBranchPorts_powerBalance_andReversal`: the headline
  statement, combining the power balance with simultaneous reversal
  of one branch, its voltage and its current.

## iii. Table of contents

- A. Electrical incidence and its entries
- B. Branch voltage from potentials
- C. Power balance
- D. Branch reversal
- E. Concrete witnesses

## iv. References

- L. O. Chua, C. A. Desoer and E. S. Kuh, *Linear and Nonlinear
  Circuits*, McGraw-Hill, 1987: the incidence matrix, Tellegen's
  theorem, and the passive sign convention for branch and port
  power.
-/

@[expose] public section

namespace PhyslibExt.Circuits.ArcPortSigns

open Matrix

/-! ## A. Electrical incidence and its entries -/

/-- The electrical incidence: the negation of the signed graph incidence, so
the tail is positive and the head is negative. -/
def electricalIncidence {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]
    [DecidableEq E] (tail head : E → V) : Matrix V E ℝ :=
  -MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix tail head

/-- The electrical incidence is the negation of the graph incidence. -/
lemma electricalIncidence_eq_neg_incidence {V : Type*} [Fintype V] [DecidableEq V]
    {E : Type*} [Fintype E] [DecidableEq E] (tail head : E → V) :
    electricalIncidence tail head =
      -MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix tail head := by
  rfl

/-- Entry of the electrical incidence: `+1` at the tail, `-1` at the head. -/
lemma electricalIncidence_apply {V : Type*} [Fintype V] [DecidableEq V] {E : Type*}
    [Fintype E] [DecidableEq E] (tail head : E → V) (n : V) (e : E) :
    electricalIncidence tail head n e =
      (if tail e = n then (1 : ℝ) else 0) - (if head e = n then 1 else 0) := by
  simp only [electricalIncidence, MathlibExt.Combinatorics.Graph.ArcNetwork.incidenceMatrix,
    Matrix.neg_apply]
  ring

/-- A loop branch, whose tail and head coincide, has a zero column. -/
lemma electricalIncidence_loop_eq_zero {V : Type*} [Fintype V] [DecidableEq V]
    {E : Type*} [Fintype E] [DecidableEq E] (tail head : E → V) (e : E)
    (hloop : tail e = head e) (n : V) :
    electricalIncidence tail head n e = 0 := by
  rw [electricalIncidence_apply, hloop, sub_self]

/-- Two distinct branch identifiers with the same tail and head have the same
incidence column; branch identity is retained by the identifier index. -/
lemma electricalIncidence_eq_of_same_endpoints {V : Type*} [Fintype V] [DecidableEq V]
    {E : Type*} [Fintype E] [DecidableEq E] (tail head : E → V) (e₁ e₂ : E)
    (htail : tail e₁ = tail e₂) (hhead : head e₁ = head e₂) (n : V) :
    electricalIncidence tail head n e₁ = electricalIncidence tail head n e₂ := by
  rw [electricalIncidence_apply, electricalIncidence_apply, htail, hhead]

/-! ## B. Branch voltage from potentials -/

/-- Potential form of branch voltage: a voltage given by the transposed
electrical incidence applied to node potentials is, at each branch, the tail
potential minus the head potential. -/
lemma branchVoltage_eq_tail_sub_head {V : Type*} [Fintype V] [DecidableEq V]
    {E : Type*} [Fintype E] [DecidableEq E] (tail head : E → V) (phi : V → ℝ)
    (v : E → ℝ) (hKVL : v = (electricalIncidence tail head).transpose *ᵥ phi) (e : E) :
    v e = phi (tail e) - phi (head e) := by
  rw [hKVL]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, electricalIncidence_apply,
    sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq _ _ _, Finset.sum_ite_eq _ _ _]
  simp

/-! ## C. Power balance -/

/-- Branch power balance in sum form: under node current balance with an
independently supplied injection and the potential definition of branch
voltage, total branch power equals total node power. This is Tellegen's
theorem for the oriented branch model. -/
theorem branchPower_eq_nodePower {V : Type*} [Fintype V] [DecidableEq V] {E : Type*}
    [Fintype E] [DecidableEq E] (tail head : E → V) (phi j : V → ℝ) (v i : E → ℝ)
    (hKCL : electricalIncidence tail head *ᵥ i = j)
    (hKVL : v = (electricalIncidence tail head).transpose *ᵥ phi) :
    (∑ e : E, v e * i e) = ∑ n : V, phi n * j n := by
  change v ⬝ᵥ i = phi ⬝ᵥ j
  rw [hKVL, dotProduct_comm, dotProduct_mulVec, vecMul_transpose, hKCL, dotProduct_comm]

/-- Branch power balance in dot-product form, the same identity as
`branchPower_eq_nodePower`. -/
theorem branchPower_eq_nodePower_dotProduct {V : Type*} [Fintype V] [DecidableEq V]
    {E : Type*} [Fintype E] [DecidableEq E] (tail head : E → V) (phi j : V → ℝ)
    (v i : E → ℝ) (hKCL : electricalIncidence tail head *ᵥ i = j)
    (hKVL : v = (electricalIncidence tail head).transpose *ᵥ phi) :
    v ⬝ᵥ i = phi ⬝ᵥ j := by
  rw [hKVL, dotProduct_comm, dotProduct_mulVec, vecMul_transpose, hKCL, dotProduct_comm]

/-! ## D. Branch reversal -/

/-- Reversing one branch together with its current preserves node current
balance: the reversed incidence applied to the reversed current is the
original nodal injection. -/
lemma mulVec_reversedBranch_eq {V : Type*} [Fintype V] [DecidableEq V] {E : Type*}
    [Fintype E] [DecidableEq E] (tail head : E → V) (i : E → ℝ) (e₀ : E) :
    electricalIncidence (Function.update tail e₀ (head e₀))
        (Function.update head e₀ (tail e₀)) *ᵥ Function.update i e₀ (-i e₀) =
      electricalIncidence tail head *ᵥ i := by
  funext n
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e = e₀
  · subst he
    simp only [Function.update_self]
    rw [electricalIncidence_apply, electricalIncidence_apply,
      Function.update_self, Function.update_self]
    ring
  · simp only [Function.update_of_ne he]
    rw [electricalIncidence_apply, electricalIncidence_apply,
      Function.update_of_ne he, Function.update_of_ne he]

/-- Reversing one branch negates its potential-defined voltage and leaves
every other branch voltage unchanged. -/
lemma transpose_mulVec_reversedBranch_eq {V : Type*} [Fintype V] [DecidableEq V]
    {E : Type*} [Fintype E] [DecidableEq E] (tail head : E → V) (phi : V → ℝ) (e₀ : E) :
    (electricalIncidence (Function.update tail e₀ (head e₀))
        (Function.update head e₀ (tail e₀))).transpose *ᵥ phi =
      Function.update ((electricalIncidence tail head).transpose *ᵥ phi) e₀
        (-((electricalIncidence tail head).transpose *ᵥ phi) e₀) := by
  funext e
  by_cases he : e = e₀
  · subst he
    simp only [Function.update_self, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [electricalIncidence_apply, electricalIncidence_apply,
      Function.update_self, Function.update_self]
    ring
  · simp only [Function.update_of_ne he, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro n _
    rw [electricalIncidence_apply, electricalIncidence_apply,
      Function.update_of_ne he, Function.update_of_ne he]

/-- Reversing one branch together with its voltage and current preserves
total branch power. -/
lemma branchPower_reversedBranch_eq {V : Type*} [Fintype V] [DecidableEq V]
    {E : Type*} [Fintype E] [DecidableEq E] (v i : E → ℝ) (e₀ : E) :
    Function.update v e₀ (-v e₀) ⬝ᵥ Function.update i e₀ (-i e₀) = v ⬝ᵥ i := by
  simp only [dotProduct]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e = e₀
  · subst he
    simp only [Function.update_self, neg_mul_neg]
  · simp only [Function.update_of_ne he]

/-- Headline correctness: the potential definition of voltage and node
current balance give the power balance, and simultaneous reversal of one
branch, its voltage and its current preserves both the nodal injection and
the potential-defined voltage up to the stated sign change. -/
theorem orientedBranchPorts_powerBalance_andReversal {V : Type*} [Fintype V]
    [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E] (tail head : E → V)
    (phi j : V → ℝ) (v i : E → ℝ) (hKCL : electricalIncidence tail head *ᵥ i = j)
    (hKVL : v = (electricalIncidence tail head).transpose *ᵥ phi) (e₀ : E) :
    (∑ e : E, v e * i e) = (∑ n : V, phi n * j n) ∧
      electricalIncidence (Function.update tail e₀ (head e₀))
          (Function.update head e₀ (tail e₀)) *ᵥ Function.update i e₀ (-i e₀) = j ∧
      (electricalIncidence (Function.update tail e₀ (head e₀))
          (Function.update head e₀ (tail e₀))).transpose *ᵥ phi =
        Function.update v e₀ (-v e₀) := by
  refine ⟨?_, ?_, ?_⟩
  · exact branchPower_eq_nodePower tail head phi j v i hKCL hKVL
  · rw [mulVec_reversedBranch_eq]
    exact hKCL
  · rw [transpose_mulVec_reversedBranch_eq, ← hKVL]

/-! ## E. Concrete witnesses -/

/-- Two-node witness: one branch from node `0` to node `1`, potentials
`3` and `1`, branch current `5`. Branch power and node power are both `10`. -/
lemma twoNode_branchPower_example :
    (∑ e : Fin 1, (![2] : Fin 1 → ℝ) e * (![5] : Fin 1 → ℝ) e) =
      ∑ n : Fin 2, (![3, 1] : Fin 2 → ℝ) n * (![5, -5] : Fin 2 → ℝ) n := by
  simp only [Fin.sum_univ_one, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- Three-node cycle witness: three branches forming a directed cycle,
unit current on each, potentials `3`, `1`, `0`. The nodal injection is zero
and total branch power is zero. -/
lemma threeNodeCycle_power_example :
    (∑ e : Fin 3, (![2, 1, -3] : Fin 3 → ℝ) e * (![1, 1, 1] : Fin 3 → ℝ) e) =
      ∑ n : Fin 3, (![3, 1, 0] : Fin 3 → ℝ) n * (![0, 0, 0] : Fin 3 → ℝ) n := by
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  norm_num

/-- Negative witness: flipping one branch current while holding the
incidence, the potentials and the externally specified injection fixed
breaks the power identity, because current balance is then violated. -/
lemma flippedCurrent_breaks_powerBalance_example :
    (![2] : Fin 1 → ℝ) ⬝ᵥ (![-5] : Fin 1 → ℝ) ≠
      (![3, 1] : Fin 2 → ℝ) ⬝ᵥ (![5, -5] : Fin 2 → ℝ) := by
  simp only [dotProduct, Fin.sum_univ_one, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have h : (2 : ℝ) * -5 < 3 * 5 + 1 * -5 := by norm_num
  exact h.ne

end PhyslibExt.Circuits.ArcPortSigns
