/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC SUM is NP-complete

Source:
E. Kubicka and A. J. Schwenk, "An introduction to chromatic sums", Proceedings of the 17th ACM
Annual Computer Science Conference (1989), 39-45, doi:10.1145/75427.75430;
D. Marx, "A short proof of the NP-completeness of minimum sum interval coloring", Operations
Research Letters 33(4) (2005), 382-384, doi:10.1016/j.orl.2004.07.006.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.PNat.Basic
public import WantedExt.Complexity.NPComplete.GraphColoringWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChromaticSum

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-!
# CHROMATIC SUM is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K`.

QUESTION: is there a proper coloring `c : V → {1, 2, 3, …}` of `G` by positive integers (adjacent
vertices get different colors) whose sum `∑_{v ∈ V} c(v)` is at most `K`?

This is the decision version of MINIMUM COLOR SUM (minimum sum coloring): the chromatic sum of
`G` is the least sum of a proper coloring by positive integers. Marx (2005, Section 1): "If the
vertices of a graph are properly colored using positive integers, then the sum of the coloring
is the sum of the numbers assigned to the vertices. The chromatic sum of a graph is the smallest
sum that a proper coloring can have. [...] It was shown by Kubicka and Schwenk that minimum sum
coloring is NP-hard in general"; Marx's Theorem 2.1 proves it NP-hard already on interval graphs.
The paper of Kubicka and Schwenk was not available. Membership in NP: a coloring is a
certificate; every color is at most the sum, hence at most `K`.

The instance, the graph and the simple-graph condition are those of
`WantedExt.Complexity.NPComplete.GraphColoringWanted` (`GraphColoring.GraphColoringInstance`: a
vertex count `n`, vertices `Fin n`, an edge list and the bound; `GraphColoring.Graph`;
`GraphColoring.WellFormed`), here with the bound read as the sum bound `K`. A proper coloring by
positive integers is Mathlib's `SimpleGraph.Coloring` with color type `ℕ+`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`
(`GraphColoring.WellFormed`), and `0 < K`. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ 0 < i.2.2

/-- Some proper coloring of the graph by positive integers has sum at most `K`. -/
def ChromaticSumFeasible (i : GraphColoringInstance) : Prop :=
  ∃ c : (Graph i).Coloring ℕ+, ∑ v, (c v : ℕ) ≤ i.2.2

open Classical in
/-- CHROMATIC SUM as a decision problem over bitstrings. -/
noncomputable def chromaticSumDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ ChromaticSumFeasible i)
  | none => false

/-- **CHROMATIC SUM is NP-complete.** Source: Kubicka and Schwenk (1989); Marx (2005). -/
public theorem_wanted chromaticSum_npComplete :
    chromaticSumDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chromaticSumDec

end MetaMathlibExt.Complexity.NPComplete.ChromaticSum
