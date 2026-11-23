/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAX CUT for cographs with edge weights 1 and 2 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND16] MAX CUT, p. 210 (the problem);
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 8 (1987), 438-448,
doi:10.1016/0196-6774(87)90021-6 (records Bodlaender's result: MAX CUT is in P for cographs in
the unweighted version, and NP-complete for cographs "if even just weights 1 and 2 are allowed",
citing H. L. Bodlaender, "The maximum cut and minimum cut into bounded sets problems of
cographs", manuscript, June 1987; the manuscript was not available).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MaxCutWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaxCutCographsWeightsOneTwo

/-!
# MAX CUT for cographs with edge weights 1 and 2 is NP-complete

INSTANCE: a cograph `G = (V, E)`, a weight `w(e) ∈ {1, 2}` for each edge `e ∈ E`, and a positive
integer `K`.
QUESTION: is there a partition of `V` into disjoint sets `V₁` and `V₂` such that the sum of the
weights of the edges from `E` that have one endpoint in `V₁` and one endpoint in `V₂` is at
least `K`?

This is MAX CUT ([ND16], whose weights are positive integers) restricted to cographs with every
weight 1 or 2. Johnson's column records Bodlaender's result that the unweighted problem
(`MaxCutWanted`) is polynomial for cographs, while this restriction is NP-complete.

The vertices are `0, ..., n - 1`; the weighted edge list holds triples `(u, v, w)`. Its edges
`(u, v)` form a simple edge list in the sense of `MaxCut.WellFormed` (no repeated edge in either
orientation, no loop, endpoints in range), which `WellFormed` reuses. A cograph is a graph with no
induced path on four vertices (Corneil, Lerchs and Stewart Burlingham 1981), as in
`AchromaticNumberCographsWanted` and `CographEditingWanted`: Mathlib's
`(SimpleGraph.pathGraph 4).IsIndContained` fails for the graph
`Cslib.Complexity.Karp.edgeGraph n E`. As in `MaxCutWanted`, the partition is `V₁ = S`,
`V₂ = V - S`, and the question is witnessed by a sublist of crossing edges of total weight at
least `K` (weights are positive, so this is the same as the full crossing weight being at
least `K`). Numbers use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), the weighted edge list of triples
`(u, v, w)` (edge `{u, v}` of weight `w`), and the bound `K`. -/
abbrev MaxCutCographsWeightsOneTwoInstance := ℕ × List (ℕ × ℕ × ℕ) × ℕ

/-- The edges `(u, v)` of the weighted edge list. -/
def edges (i : MaxCutCographsWeightsOneTwoInstance) : List (ℕ × ℕ) :=
  i.2.1.map fun e => (e.1, e.2.1)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MaxCutCographsWeightsOneTwoInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (edges i)

/-- Well-formedness of an instance: the edges form a simple edge list on `0, ..., n - 1`
(`MaxCut.WellFormed`), every weight is `1` or `2`, the graph is a cograph (no induced path on
four vertices), and `0 < K`. -/
def WellFormed (i : MaxCutCographsWeightsOneTwoInstance) : Prop :=
  MaxCut.WellFormed (i.1, edges i, i.2.2) ∧ (∀ e ∈ i.2.1, e.2.2 = 1 ∨ e.2.2 = 2) ∧
    ¬ (SimpleGraph.pathGraph 4).IsIndContained (Graph i) ∧ 0 < i.2.2

/-- A partition `V₁ = S`, `V₂ = V - S` and edges of total weight at least `K`, each with one
endpoint in `V₁` and one in `V₂`. -/
def MaxCutCographsWeightsOneTwoFeasible (i : MaxCutCographsWeightsOneTwoInstance) : Prop :=
  ∃ S : Finset ℕ, (∀ v ∈ S, v < i.1) ∧
    ∃ cut : List (ℕ × ℕ × ℕ), cut.Sublist i.2.1 ∧ i.2.2 ≤ (cut.map fun e => e.2.2).sum ∧
      ∀ e ∈ cut, (e.1 ∈ S ∧ e.2.1 ∉ S) ∨ (e.1 ∉ S ∧ e.2.1 ∈ S)

open Classical in
/-- MAX CUT for cographs with edge weights 1 and 2, as a decision problem over bitstrings. -/
noncomputable def maxCutCographsWeightsOneTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxCutCographsWeightsOneTwoInstance) x with
  | some i => decide (WellFormed i ∧ MaxCutCographsWeightsOneTwoFeasible i)
  | none => false

/-- **MAX CUT for cographs with edge weights 1 and 2 is NP-complete.** Source: Garey and Johnson
(1979), [ND16]; Johnson (1987), recording Bodlaender (1987). -/
public theorem_wanted maxCutCographsWeightsOneTwo_npComplete :
    maxCutCographsWeightsOneTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maxCutCographsWeightsOneTwoDec

end MetaMathlibExt.Complexity.NPComplete.MaxCutCographsWeightsOneTwo
