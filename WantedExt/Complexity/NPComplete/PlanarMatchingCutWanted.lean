/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MATCHING CUT on planar graphs is NP-complete

Source:
P. Bonsma, "The complexity of the matching-cut problem for planar graphs and other graph
classes", Journal of Graph Theory 62 (2009), 109-126, doi:10.1002/jgt.20390.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import WantedExt.Complexity.NPComplete.MatchingCutWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarMatchingCut

open MetaMathlibExt.Complexity.NPComplete.MatchingCut

/-!
# MATCHING CUT on planar graphs is NP-complete

INSTANCE: a planar graph `G = (V, E)`.
QUESTION: does `G` have a matching cut, that is, an edge cut that is also a matching?

The instance, its well-formedness and the question are those of
`WantedExt.Complexity.NPComplete.MatchingCutWanted` (a simple graph on `Fin n` given by an edge
list; the question asks for a decomposition, a red/blue colouring using both colours in which
every vertex has at most one neighbour of the other colour, which is exactly a matching cut).
The restriction adds that the graph is planar, as MathlibExt's shared predicate
`SimpleGraph.IsPlanar` (a crossing-free straight-line drawing; by Fáry's theorem this is
planarity for finite simple graphs). Bonsma proves NP-completeness for planar graphs of maximum
degree four, and also for planar graphs of girth five.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed MATCHING CUT instance whose graph is
planar. -/
def WellFormed (i : MatchingCutInstance) : Prop :=
  MatchingCut.WellFormed i ∧ (Graph i).IsPlanar

open Classical in
/-- MATCHING CUT on planar graphs as a decision problem over bitstrings. -/
noncomputable def planarMatchingCutDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MatchingCutInstance) x with
  | some i => decide (WellFormed i ∧ MatchingCutFeasible i)
  | none => false

/-- **MATCHING CUT on planar graphs is NP-complete.** Source: Bonsma (2009). -/
public theorem_wanted planarMatchingCut_npComplete :
    planarMatchingCutDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L planarMatchingCutDec

end MetaMathlibExt.Complexity.NPComplete.PlanarMatchingCut
