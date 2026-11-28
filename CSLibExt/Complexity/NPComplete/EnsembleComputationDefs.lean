/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ENSEMBLE COMPUTATION: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO9] ENSEMBLE
COMPUTATION; the proof is Theorem 3.6 in Section 3.2.2 of the book (local
replacement, a transformation from VERTEX COVER).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EnsembleComputation

/-- An instance: the size `m` of `A` (elements `Fin m`), the collection `C` as a list of
strictly increasing lists of elements, and the bound `J`. -/
abbrev EnsembleComputationInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: every member of `C` is a strictly increasing list of
elements of `A`, no member is listed twice, and `J` is positive. -/
def WellFormed (i : EnsembleComputationInstance) : Prop :=
  (∀ c ∈ i.2.1, c.Pairwise (· < ·) ∧ ∀ a ∈ c, a < i.1) ∧ i.2.1.Nodup ∧ 0 < i.2.2

/-- The subset of `Fin m` listed by `c` (entries out of range are dropped). -/
def toSubset (m : ℕ) (c : List ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun a => (a : ℕ) ∈ c

/-- The value of an operand of operation `i`: `Sum.inl a` is `{a}`, `Sum.inr k` is `z k`. -/
def operandValue {m j : ℕ} (z : Fin j → Finset (Fin m)) : Fin m ⊕ Fin j → Finset (Fin m)
  | .inl a => {a}
  | .inr k => z k

/-- A sequence of `j ≤ J` union operations `zᵢ ← xᵢ ∪ yᵢ` with disjoint operands, each a
singleton or an earlier result, such that every member of `C` equals some `zᵢ`. -/
def EnsembleComputationFeasible (i : EnsembleComputationInstance) : Prop :=
  ∃ j ≤ i.2.2, ∃ z : Fin j → Finset (Fin i.1), ∃ x y : Fin j → Fin i.1 ⊕ Fin j,
    (∀ t k, x t = .inr k → k < t) ∧ (∀ t k, y t = .inr k → k < t) ∧
    (∀ t, Disjoint (operandValue z (x t)) (operandValue z (y t))) ∧
    (∀ t, z t = operandValue z (x t) ∪ operandValue z (y t)) ∧
    ∀ c ∈ i.2.1, ∃ t, z t = toSubset i.1 c

open Classical in
/-- ENSEMBLE COMPUTATION as a decision problem over bitstrings. -/
noncomputable def ensembleComputationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EnsembleComputationInstance) x with
  | some i => decide (WellFormed i ∧ EnsembleComputationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EnsembleComputation
