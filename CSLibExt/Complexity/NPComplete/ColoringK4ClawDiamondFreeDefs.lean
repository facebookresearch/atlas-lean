/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH K-COLORABILITY on (K_4, claw, diamond)-free graphs: definitions

Source:
D. Král', J. Kratochvíl, Z. Tuza, and G. J. Woeginger, "Complexity of coloring graphs without
forbidden induced subgraphs", Graph-Theoretic Concepts in Computer Science (WG 2001), LNCS
2204, 254-262, doi:10.1007/3-540-45477-2_23 (3-colorability is NP-complete for
(K₄, K₁,₃, diamond)-free graphs);
P. A. Golovach, M. Johnson, D. Paulusma, and J. Song, "A survey on the computational complexity
of coloring graphs with forbidden subgraphs", Journal of Graph Theory 84 (2017), 331-363,
doi:10.1002/jgt.22028, proof of Theorem 21(i).2 (records that result);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ColoringK4ClawDiamondFree

/-- The diamond: `K_4` on `Fin 4` minus the edge `{0, 1}`. -/
abbrev diamond : SimpleGraph (Fin 4) := (⊤ : SimpleGraph (Fin 4)).deleteEdges {s(0, 1)}

/-- Well-formedness of an instance: a well-formed GRAPH K-COLORABILITY instance (a simple graph
given by an edge list), `K` is positive, the graph has no `K_4`, and neither the claw
`K_{1,3}` nor the diamond is an induced subgraph of it. -/
def WellFormed (i : GraphColoring.GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ 0 < i.2.2 ∧ (GraphColoring.Graph i).CliqueFree 4 ∧
    ¬ (completeBipartiteGraph (Fin 1) (Fin 3)).IsIndContained (GraphColoring.Graph i) ∧
    ¬ diamond.IsIndContained (GraphColoring.Graph i)

open Classical in
/-- GRAPH K-COLORABILITY on `(K_4, claw, diamond)`-free graphs as a decision problem over
bitstrings. -/
noncomputable def coloringK4ClawDiamondFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphColoring.GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ColoringK4ClawDiamondFree
