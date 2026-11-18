/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Graph.ArcNetwork
public import PhyslibExt.Circuits.TellegenPowerBalance
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Ring

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
balance unchanged. The power balance itself is the shared matrix
form `PhyslibExt.Circuits.TellegenPowerBalance.branchPower_eq_nodePower`
applied to the electrical incidence. Distinct branch identifiers that
join the same pair of nodes keep distinct columns as functions of the
identifier, and a branch whose tail and head coincide has a zero
column.

## ii. Key results

- `branchVoltage_eq_tail_sub_head`: a potential-defined branch
  voltage is the tail potential minus the head potential.
- `orientedBranchPorts_powerBalance_andReversal`: the headline
  statement, combining the power balance, in sum form, with
  simultaneous reversal of one branch, its voltage and its current.

## iii. Table of contents

- A. Electrical incidence and its entries
- B. Branch voltage from potentials
- C. Branch reversal
- D. Power balance and reversal

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

/-! ## C. Branch reversal -/

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
lemma branchPower_reversedBranch_eq
    {E : Type*} [Fintype E] [DecidableEq E] (v i : E → ℝ) (e₀ : E) :
    Function.update v e₀ (-v e₀) ⬝ᵥ Function.update i e₀ (-i e₀) = v ⬝ᵥ i := by
  simp only [dotProduct]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e = e₀
  · subst he
    simp only [Function.update_self, neg_mul_neg]
  · simp only [Function.update_of_ne he]

/-! ## D. Power balance and reversal -/

/-- Headline correctness: the potential definition of voltage and node
current balance give the power balance, and simultaneous reversal of one
branch, its voltage and its current preserves both the nodal injection and
the potential-defined voltage up to the stated sign change. -/
lemma orientedBranchPorts_powerBalance_andReversal {V : Type*} [Fintype V]
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
  · exact PhyslibExt.Circuits.TellegenPowerBalance.branchPower_eq_nodePower
      (electricalIncidence tail head) phi j v i hKVL hKCL
  · rw [mulVec_reversedBranch_eq]
    exact hKCL
  · rw [transpose_mulVec_reversedBranch_eq, ← hKVL]

end PhyslibExt.Circuits.ArcPortSigns
