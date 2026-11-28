/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SET BASIS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP7] SET BASIS;
L. J. Stockmeyer, "The set basis problem is NP-complete", Report RC-5431,
IBM Research Center, Yorktown Heights, NY (1975).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SetBasis

/-- An instance: the size `m` of `S` (elements `Fin m`), the collection `C` as a list of
strictly increasing lists of elements, and the bound `K`. -/
abbrev SetBasisInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: every member of `C` is a strictly increasing list of
elements of `S`, no member is listed twice (so the list length is `|C|`), and
`0 < K ≤ |C|`. -/
def WellFormed (i : SetBasisInstance) : Prop :=
  (∀ c ∈ i.2.1, c.Pairwise (· < ·) ∧ ∀ a ∈ c, a < i.1) ∧ i.2.1.Nodup ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

/-- The subset of `Fin m` listed by `c` (entries out of range are dropped). -/
def toSubset (m : ℕ) (c : List ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun a => (a : ℕ) ∈ c

/-- A collection `B` of exactly `K` subsets of `S` such that every member of `C` is the union
of some subcollection of `B`. -/
def SetBasisFeasible (i : SetBasisInstance) : Prop :=
  ∃ B : Finset (Finset (Fin i.1)), B.card = i.2.2 ∧
    ∀ c ∈ i.2.1, ∃ D ⊆ B, D.sup id = toSubset i.1 c

open Classical in
/-- SET BASIS as a decision problem over bitstrings. -/
noncomputable def setBasisDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SetBasisInstance) x with
  | some i => decide (WellFormed i ∧ SetBasisFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SetBasis
