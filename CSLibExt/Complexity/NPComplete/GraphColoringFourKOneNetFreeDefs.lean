/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH K-COLORABILITY ON (4K₁, NET)-FREE GRAPHS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (CHROMATIC
NUMBER), the problem restricted here;
D. Schindl, "Some new hereditary classes where graph coloring remains NP-hard", Discrete
Mathematics 295 (2005), 197-202, doi:10.1016/j.disc.2005.03.003;
P. A. Golovach, M. Johnson, D. Paulusma, and J. Song, "A survey on the computational complexity
of coloring graphs with forbidden subgraphs", Journal of Graph Theory 84 (2017), 331-363,
doi:10.1002/jgt.22028, arXiv:1407.1482, Theorem 17 (Schindl's theorem).
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringTwoKTwoNetFreeDefs
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoringFourKOneNetFree

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-- Well-formedness of an instance: a well-formed GRAPH K-COLORABILITY instance with `0 < K ≤ |V|`
whose graph has no induced `4K₁` (no independent set of four vertices) and no induced net. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ (0 < i.2.2 ∧ i.2.2 ≤ i.1) ∧
    ¬ (⊥ : SimpleGraph (Fin 4)).IsIndContained (Graph i) ∧
    ¬ GraphColoringTwoKTwoNetFree.net.IsIndContained (Graph i)

open Classical in
/-- GRAPH K-COLORABILITY ON (4K₁, NET)-FREE GRAPHS as a decision problem over bitstrings. -/
noncomputable def graphColoringFourKOneNetFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GraphColoringFourKOneNetFree
