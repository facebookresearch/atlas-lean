/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPTIMUM INDEX SELECTION is NP-complete

Source:
D. Comer, "The difficulty of optimum index selection", ACM Transactions on Database Systems 3
(1978), 440-445, doi:10.1145/320289.320296 (read in the report version, Purdue University
Computer Sciences Department, CSD-TR 248, September 1977), Section 2 (the Optimum Index
Selection Problem, OISP) and Theorem 1 (OISP is NP-complete, by a reduction from 3-SAT that
builds a file with attribute values `0` and `1`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OptimumIndexSelection

/-!
# OPTIMUM INDEX SELECTION is NP-complete

INSTANCE: a file `F` with `n` records and `k` attributes, and an integer `p`. QUESTION: does
there exist an indexing set for `F` with size no more than `p`?

Comer (Section 2) defines a file as a set of `n` records `r = (v₁, …, v_k)`, `vᵢ` a value of
the `i`-th attribute (a single relation in the relational model). Attribute `i` distinguishes
two records iff they differ in the `i`-th component, and `I ⊆ {1, …, k}` is an indexing set iff
any pair of records in `F` is distinguished by some attribute in `I`; its size is `|I|`. Here
records are lists of `k` natural numbers (attribute values from finite sets, numbered), the file
is a duplicate-free list of records (a set, as a relation is), the attributes are `Fin k`, and
an indexing set is a `Finset (Fin k)`.

Comer proves OISP NP-complete (Theorem 1) by a reduction from 3-SAT whose files take only the
values `0` and `1` ("the result is strong in that it applies even if the attribute values are
restricted to the binary range"); the files here are unrestricted. For binary files the problem
is MINIMUM TEST SET (`MinimumTestSetWanted`) with the records as the elements and the attributes
as the tests; with more than two values an attribute is one test that separates every pair of
records with different values. Membership in NP: the indexing set is the certificate.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **OPTIMUM INDEX SELECTION is NP-complete.** Source: Comer (1978), Section 2 and
Theorem 1. -/
public theorem_wanted optimumIndexSelection_npComplete :
    optimumIndexSelectionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L optimumIndexSelectionDec

end MetaMathlibExt.Complexity.NPComplete.OptimumIndexSelection
