/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ACHROMATIC NUMBER OF TREES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT5] ACHROMATIC NUMBER;
N. Cairnie and K. Edwards, "Some results on the achromatic number", Journal of Graph Theory
26 (1997), 129-136, doi:10.1002/(SICI)1097-0118(199711)26:3<129::AID-JGT3>3.0.CO;2-T.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.AchromaticNumberWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AchromaticNumberTrees

open MetaMathlibExt.Complexity.NPComplete.AchromaticNumber (AchromaticNumberInstance)

/-!
# ACHROMATIC NUMBER OF TREES is NP-complete

INSTANCE: a tree `G = (V, E)` and a positive integer `K`.
QUESTION: does `G` have a complete proper coloring with at least `K` colors, i.e., is the
achromatic number of `G` at least `K`?

This is ACHROMATIC NUMBER (`AchromaticNumberWanted`) restricted to trees.

A tree is a connected acyclic graph, Mathlib's `SimpleGraph.IsTree`. Cairnie and Edwards
prove that determining the achromatic number of a tree is NP-hard; membership in NP is that of
ACHROMATIC NUMBER.

The instance and the question are those of `AchromaticNumberWanted`, reused unchanged: vertex count,
edge list on `Fin n` and bound `K`, with `AchromaticNumber.WellFormed` and
`AchromaticNumber.AchromaticNumberFeasible` (some `q ≥ K` and a proper coloring with colors
`0, …, q - 1`, all used, every two of them adjacent somewhere). The restriction adds to
well-formedness that the graph `Cslib.Complexity.Karp.edgeGraph n E` is a tree
(`SimpleGraph.IsTree`: connected and acyclic), and that `K` is positive, as in the source.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed ACHROMATIC NUMBER instance whose graph is
a tree, with `0 < K`. -/
def WellFormed (i : AchromaticNumberInstance) : Prop :=
  AchromaticNumber.WellFormed i ∧
    (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).IsTree ∧ 0 < i.2.2

open Classical in
/-- ACHROMATIC NUMBER OF TREES as a decision problem over bitstrings. -/
noncomputable def achromaticNumberTreesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := AchromaticNumberInstance) x with
  | some i => decide (WellFormed i ∧ AchromaticNumber.AchromaticNumberFeasible i)
  | none => false

/-- **ACHROMATIC NUMBER OF TREES is NP-complete.** Source: Garey and Johnson (1979), [GT5];
Cairnie and Edwards (1997). -/
public theorem_wanted achromaticNumberTrees_npComplete :
    achromaticNumberTreesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L achromaticNumberTreesDec

end MetaMathlibExt.Complexity.NPComplete.AchromaticNumberTrees
