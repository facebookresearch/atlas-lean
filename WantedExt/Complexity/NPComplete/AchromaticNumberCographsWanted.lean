/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ACHROMATIC NUMBER OF COGRAPHS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT5] ACHROMATIC NUMBER;
H. L. Bodlaender, "Achromatic number is NP-complete for cographs and interval graphs",
Information Processing Letters 31 (1989), 135-138, doi:10.1016/0020-0190(89)90221-4.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.AchromaticNumberWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AchromaticNumberCographs

open MetaMathlibExt.Complexity.NPComplete.AchromaticNumber (AchromaticNumberInstance)

/-!
# ACHROMATIC NUMBER OF COGRAPHS is NP-complete

INSTANCE: a cograph `G = (V, E)` and a positive integer `K`.
QUESTION: does `G` have a complete proper coloring with at least `K` colors, i.e., is the
achromatic number of `G` at least `K`?

This is ACHROMATIC NUMBER (`AchromaticNumberWanted`) restricted to cographs.

A cograph is a graph built from single vertices by complementation and disjoint union;
equivalently (Corneil, Lerchs and Stewart Burlingham 1981), a graph with no induced path on four
vertices. The module uses the induced-path characterization: Mathlib's
`(SimpleGraph.pathGraph 4).IsIndContained G` fails. Bodlaender proves ACHROMATIC NUMBER
NP-complete for cographs and for interval graphs.

The instance and the question are those of `AchromaticNumberWanted`, reused unchanged: vertex count,
edge list on `Fin n` and bound `K`, with `AchromaticNumber.WellFormed` and
`AchromaticNumber.AchromaticNumberFeasible` (some `q ≥ K` and a proper coloring with colors
`0, …, q - 1`, all used, every two of them adjacent somewhere). The restriction adds to
well-formedness that the graph `Cslib.Complexity.Karp.edgeGraph n E` is a cograph (`P_4`-free), and
that `K` is positive, as in the source.

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
a cograph (no induced path on four vertices), with `0 < K`. -/
def WellFormed (i : AchromaticNumberInstance) : Prop :=
  AchromaticNumber.WellFormed i ∧
    ¬ (SimpleGraph.pathGraph 4).IsIndContained (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1) ∧
    0 < i.2.2

open Classical in
/-- ACHROMATIC NUMBER OF COGRAPHS as a decision problem over bitstrings. -/
noncomputable def achromaticNumberCographsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := AchromaticNumberInstance) x with
  | some i => decide (WellFormed i ∧ AchromaticNumber.AchromaticNumberFeasible i)
  | none => false

/-- **ACHROMATIC NUMBER OF COGRAPHS is NP-complete.** Source: Garey and Johnson (1979), [GT5];
Bodlaender (1989). -/
public theorem_wanted achromaticNumberCographs_npComplete :
    achromaticNumberCographsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L achromaticNumberCographsDec

end MetaMathlibExt.Complexity.NPComplete.AchromaticNumberCographs
