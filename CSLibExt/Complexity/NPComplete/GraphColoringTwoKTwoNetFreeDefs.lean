/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH K-COLORABILITY ON (2K₂, NET)-FREE GRAPHS: definitions

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

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphColoringTwoKTwoNetFree

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-- `2K₂`: two disjoint edges. -/
abbrev twoKTwo : SimpleGraph (Fin 2 ⊕ Fin 2) :=
  SimpleGraph.pathGraph 2 ⊕g SimpleGraph.pathGraph 2

/-- The net: the triangle `0, 1, 2` with the pendant vertices `3, 4, 5` attached to `0, 1, 2`. -/
def net : SimpleGraph (Fin 6) :=
  Cslib.Complexity.Karp.edgeGraph 6 [(0, 1), (1, 2), (0, 2), (0, 3), (1, 4), (2, 5)]

/-- Well-formedness of an instance: a well-formed GRAPH K-COLORABILITY instance with
`0 < K ≤ |V|` whose graph has no induced `2K₂` and no induced net. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ (0 < i.2.2 ∧ i.2.2 ≤ i.1) ∧ ¬ twoKTwo.IsIndContained (Graph i) ∧
    ¬ net.IsIndContained (Graph i)

open Classical in
/-- GRAPH K-COLORABILITY ON (2K₂, NET)-FREE GRAPHS as a decision problem over bitstrings. -/
noncomputable def graphColoringTwoKTwoNetFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GraphColoringTwoKTwoNetFree
