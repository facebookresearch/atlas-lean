/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LIST COLORING is NP-complete

Source:
J. Kratochvíl and Z. Tuza, "Algorithmic complexity of list colorings", Discrete Applied
Mathematics, 1994.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ListColoring

/-!
# LIST COLORING is NP-complete

An undirected graph with an explicit finite color list for every vertex. The question is
whether there is a proper coloring choosing each vertex's color from its own list.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A list-coloring instance: vertex count, edge list, color list per vertex. -/
abbrev ListColoringInstance := ℕ × List (ℕ × ℕ) × List (List ℕ)

/-- Well-formedness of an instance. -/
def WellFormed (i : ListColoringInstance) : Prop :=
  i.2.1.Nodup ∧
    (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.length = i.1

/-- A proper coloring choosing from the given lists. -/
def ListColoringFeasible
    (i : ListColoringInstance) : Prop :=
  ∃ assign : List ℕ, assign.length = i.1 ∧
    (∀ v < i.1, assign.getD v 0 ∈ i.2.2.getD v []) ∧
    ∀ e ∈ i.2.1, assign.getD e.1 0 ≠ assign.getD e.2 0

open Classical in
/-- LIST COLORING as a decision problem over bitstrings. -/
noncomputable def listColoringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ListColoringInstance) x with
  | some i => decide (WellFormed i ∧ ListColoringFeasible i)
  | none => false

/-- **LIST COLORING is NP-complete.** Source: J. Kratochvíl and Z. Tuza, "Algorithmic
complexity of list colorings", Discrete Applied Mathematics, 1994. -/
public theorem_wanted listColoring_npComplete :
    listColoringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L listColoringDec

end MetaMathlibExt.Complexity.NPComplete.ListColoring
