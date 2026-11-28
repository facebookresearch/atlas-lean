/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDUCED MATCHING ON BIPARTITE GRAPHS: definitions

Source:
K. Cameron, "Induced matchings", Discrete Applied Mathematics 24 (1989), 97-102,
doi:10.1016/0166-218X(92)90275-F;
L. J. Stockmeyer and V. V. Vazirani, "NP-completeness of some generalizations of the maximum
matching problem", Information Processing Letters 15 (1982), 14-19,
doi:10.1016/0020-0190(82)90077-1.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MaximumInducedMatchingDefs
public import Mathlib.Combinatorics.SimpleGraph.Bipartite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaximumInducedMatchingBipartite

/-- Well-formedness of an instance: it is a well-formed MAXIMUM INDUCED MATCHING instance
(simple edge list), its graph is bipartite, and `K` is positive. -/
def WellFormed (i : MaximumInducedMatching.MaximumInducedMatchingInstance) : Prop :=
  MaximumInducedMatching.WellFormed i ∧
    (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).IsBipartite ∧ 0 < i.2.2

open Classical in
/-- INDUCED MATCHING ON BIPARTITE GRAPHS as a decision problem over bitstrings. -/
noncomputable def maximumInducedMatchingBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaximumInducedMatching.MaximumInducedMatchingInstance) x with
  | some i => decide (WellFormed i ∧ MaximumInducedMatching.MaximumInducedMatchingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MaximumInducedMatchingBipartite
