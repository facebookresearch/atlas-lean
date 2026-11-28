/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SUBGRAPH ISOMORPHISM for connected outerplanar graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT48] SUBGRAPH ISOMORPHISM (the
unrestricted problem);
M. M. Sysło, "The subgraph isomorphism problem for outerplanar graphs", Theoretical Computer
Science 17 (1982), 91-97, doi:10.1016/0304-3975(82)90133-5.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SubgraphIsomorphismDefs
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import MathlibExt.GraphTheory.BookThicknessOfSubdivisionsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SubgraphIsomorphismOuterplanar

open MetaMathlibExt.Complexity.NPComplete.SubgraphIsomorphism
  (SubgraphIsomorphismInstance GraphHost)
open MathlibExt.GraphTheory.BookThicknessOfSubdivisionsWanted (HasBookEmbedding)

/-- The pattern graph `H` of the instance. -/
def GraphPattern (i : SubgraphIsomorphismInstance) : SimpleGraph (Fin i.2.2.1) :=
  Cslib.Complexity.Karp.edgeGraph i.2.2.1 i.2.2.2

/-- Well-formedness of an instance: it is a well-formed SUBGRAPH ISOMORPHISM instance (both edge
lists simple), and the host `G` and the pattern `H` are connected and outerplanar (have a
one-page book embedding). -/
def WellFormed (i : SubgraphIsomorphismInstance) : Prop :=
  SubgraphIsomorphism.WellFormed i ∧ (GraphHost i).Connected ∧ HasBookEmbedding (GraphHost i) 1 ∧
    (GraphPattern i).Connected ∧ HasBookEmbedding (GraphPattern i) 1

open Classical in
/-- SUBGRAPH ISOMORPHISM for connected outerplanar graphs as a decision problem over
bitstrings. -/
noncomputable def subgraphIsomorphismOuterplanarDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SubgraphIsomorphismInstance) x with
  | some i => decide (WellFormed i ∧ SubgraphIsomorphism.SubgraphIsomorphismFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SubgraphIsomorphismOuterplanar
