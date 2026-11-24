/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIWAY CUT ON PLANAR GRAPHS is NP-complete

Source:
E. Dahlhaus, D. S. Johnson, C. H. Papadimitriou, P. D. Seymour and M. Yannakakis, "The
complexity of multiterminal cuts", SIAM Journal on Computing 23(4) (1994), 864-894,
doi:10.1137/S0097539792225297 (the planar problem is NP-hard when the number of terminals is not
fixed);
M. Johnson, B. Martin, S. Pandey, D. Paulusma, S. Smith and E. J. van Leeuwen, "Edge multiway cut
and node multiway cut are hard for planar subcubic graphs", 19th Scandinavian Symposium on
Algorithm Theory (SWAT 2024), LIPIcs 294 (2024), 29:1-29:17, doi:10.4230/LIPIcs.SWAT.2024.29
(Theorem 1.1: unweighted EDGE MULTIWAY CUT is NP-complete for planar subcubic graphs).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultiwayCutWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiwayCutPlanar

open MultiwayCut (MultiwayCutInstance MultiwayCutFeasible)

/-!
# MULTIWAY CUT ON PLANAR GRAPHS is NP-complete

INSTANCE: a planar graph `G = (V, E)`, a set `T ⊆ V` of terminals (its size part of the
input), and a positive integer `B`. QUESTION: is there a set of at most `B` edges whose removal
separates every pair of terminals?

This is MULTIWAY CUT (`MultiwayCutWanted`) restricted to planar graphs. The instance type, the
parent's well-formedness (simple edge list on `Fin n`, duplicate-free terminals in range) and the
question (`MultiwayCutFeasible`) are reused; planarity of the graph of the edge list
(`Cslib.Complexity.Karp.edgeGraph`) is MathlibExt's `SimpleGraph.IsPlanar` (a crossing-free
straight-line drawing; by Fáry's theorem this is planarity for finite simple graphs), and the
positivity of the bound `B` is added to the well-formedness.

Dahlhaus et al. prove the planar problem NP-hard when the number of terminals is not fixed, for
edge-weighted graphs; for unweighted simple graphs, the setting of `MultiwayCutWanted`, Johnson
et al. (Theorem 1.1) prove NP-completeness already for planar graphs of maximum degree 3.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: well formed for MULTIWAY CUT, the graph of the edge list is
planar, and the bound `B` is positive. -/
def WellFormed (i : MultiwayCutInstance) : Prop :=
  MultiwayCut.WellFormed i ∧ (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).IsPlanar ∧
    0 < i.2.2.2

open Classical in
/-- MULTIWAY CUT ON PLANAR GRAPHS as a decision problem over bitstrings. -/
noncomputable def multiwayCutPlanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := MultiwayCutInstance) x with
  | some i => decide (WellFormed i ∧ MultiwayCutFeasible i)
  | none => false

/-- **MULTIWAY CUT ON PLANAR GRAPHS is NP-complete.** Source: Dahlhaus, Johnson, Papadimitriou,
Seymour and Yannakakis (1994); Johnson, Martin, Pandey, Paulusma, Smith and van Leeuwen (2024),
Theorem 1.1. -/
public theorem_wanted multiwayCutPlanar_npComplete :
    multiwayCutPlanarDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiwayCutPlanarDec

end MetaMathlibExt.Complexity.NPComplete.MultiwayCutPlanar
