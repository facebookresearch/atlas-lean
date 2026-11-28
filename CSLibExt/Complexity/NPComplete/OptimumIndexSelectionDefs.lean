/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPTIMUM INDEX SELECTION: definitions

Source:
D. Comer, "The difficulty of optimum index selection", ACM Transactions on Database Systems 3
(1978), 440-445, doi:10.1145/320289.320296 (read in the report version, Purdue University
Computer Sciences Department, CSD-TR 248, September 1977), Section 2 (the Optimum Index
Selection Problem, OISP) and Theorem 1 (OISP is NP-complete, by a reduction from 3-SAT that
builds a file with attribute values `0` and `1`).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OptimumIndexSelection

/-- An instance: the number `k` of attributes, the records (each a list of `k` attribute
values), and the bound `p`. -/
abbrev OptimumIndexSelectionInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: every record has `k` components, and no record occurs
twice (the file is a set of records). -/
def WellFormed (i : OptimumIndexSelectionInstance) : Prop :=
  (∀ r ∈ i.2.1, r.length = i.1) ∧ i.2.1.Nodup

/-- The value `vₐ` of attribute `a` in record `r`. -/
def value (i : OptimumIndexSelectionInstance) (r : Fin i.2.1.length) (a : Fin i.1) : ℕ :=
  (i.2.1.get r).getD a 0

/-- `I` is an indexing set: any two different records of the file are distinguished by some
attribute in `I`, i.e. they differ in that component. -/
def IsIndexingSet (i : OptimumIndexSelectionInstance) (I : Finset (Fin i.1)) : Prop :=
  ∀ r s : Fin i.2.1.length, r ≠ s → ∃ a ∈ I, value i r a ≠ value i s a

/-- Some indexing set has size at most `p`. -/
def OptimumIndexSelectionFeasible (i : OptimumIndexSelectionInstance) : Prop :=
  ∃ I : Finset (Fin i.1), IsIndexingSet i I ∧ I.card ≤ i.2.2

open Classical in
/-- OPTIMUM INDEX SELECTION as a decision problem over bitstrings. -/
noncomputable def optimumIndexSelectionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OptimumIndexSelectionInstance) x with
  | some i => decide (WellFormed i ∧ OptimumIndexSelectionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.OptimumIndexSelection
