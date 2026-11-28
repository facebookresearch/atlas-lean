/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING CYCLE on planar 2-connected graphs: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 5 (1984), 147-160,
doi:10.1016/0196-6774(84)90045-2, Section 3 (the DOMINATING SET [GT2] variant whose dominating
set must form a cycle: "NP-complete for planar 2-connected graphs, but solvable in polynomial
time for outerplanar graphs"), crediting
A. Proskurowski and M. M. Sysło, "Minimum dominating cycles in outerplanar graphs", Internat. J.
Comput. Inform. Sci. 10 (1981), 127-139, doi:10.1007/BF00977745 (not available);
H. Eto, H. Kawahara, E. Miyano and N. Nonoue, "Complexity of the minimum single dominating cycle
problem for graph classes", IEICE Trans. Inf. & Syst. E101-D (2018), 574-581,
doi:10.1587/transinf.2017FCP0007, Section 1 (the definition, and the hardness on planar graphs
attributed to Proskurowski and Sysło).
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.CycleCover
public import MathlibExt.Combinatorics.SimpleGraph.Domination
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Combinatorics.SimpleGraph.VertexConnectivity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.DominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingCyclePlanarBiconnected

open MetaMathlibExt.Complexity.NPComplete.DominatingSet

/-- Well-formedness of an instance: a well-formed DOMINATING SET instance with `0 < K` whose
graph is planar and 2-connected. -/
def WellFormed (i : DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ 0 < i.2.2 ∧ (Graph i).IsPlanar ∧ (Graph i).IsVertexConnected 2

/-- Some cycle of at most `K` vertices dominates the graph. -/
def DominatingCycleFeasible (i : DominatingSetInstance) : Prop :=
  ∃ c : SimpleGraph.Cycle (Graph i), c.length ≤ i.2.2 ∧
    (Graph i).IsDominating {v | v ∈ c.walk.support}

open Classical in
/-- DOMINATING CYCLE on planar 2-connected graphs as a decision problem over bitstrings. -/
noncomputable def dominatingCyclePlanarBiconnectedDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingCycleFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DominatingCyclePlanarBiconnected
