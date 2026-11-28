/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ACHROMATIC NUMBER of complements of bipartite graphs: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT5] ACHROMATIC NUMBER, p. 191
(comment: "Remains NP-complete even if `G` is the complement of a bipartite graph and hence has
no independent set of more than two vertices.");
M. Yannakakis and F. Gavril, "Edge dominating sets in graphs", SIAM Journal on Applied
Mathematics 38 (1980), 364-372, doi:10.1137/0138030, Corollary 2.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import CSLibExt.Complexity.NPComplete.AchromaticNumberDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AchromaticNumberCoBipartite

open MetaMathlibExt.Complexity.NPComplete.AchromaticNumber (AchromaticNumberInstance)

/-- Well-formedness of an instance: a well-formed ACHROMATIC NUMBER instance whose graph is the
complement of a bipartite graph, with `0 < K ≤ |V|`. -/
def WellFormed (i : AchromaticNumberInstance) : Prop :=
  AchromaticNumber.WellFormed i ∧ (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1)ᶜ.IsBipartite ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- ACHROMATIC NUMBER of complements of bipartite graphs as a decision problem over
bitstrings. -/
noncomputable def achromaticNumberCoBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := AchromaticNumberInstance) x with
  | some i => decide (WellFormed i ∧ AchromaticNumber.AchromaticNumberFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.AchromaticNumberCoBipartite
