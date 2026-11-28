/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-COLORABILITY OF (K4, CLAW, DIAMOND)-FREE GRAPHS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY;
D. Král', J. Kratochvíl, Zs. Tuza and G. J. Woeginger, "Complexity of coloring graphs without
forbidden induced subgraphs", Graph-Theoretic Concepts in Computer Science (WG 2001), Lecture
Notes in Computer Science 2204 (2001), 254-262, doi:10.1007/3-540-45477-2_23;
P. A. Golovach, M. Johnson, D. Paulusma and J. Song, "A survey on the computational complexity of
coloring graphs with forbidden subgraphs", Journal of Graph Theory 84 (2017), 331-363,
doi:10.1002/jgt.22028, Section 3, proof of Theorem 21 (i) 2 (arXiv:1407.1482v8);
ISGCI (Information System on Graph Classes and their Inclusions), class `(K_4, claw, diamond)`-free
(gc_919), problem 3-Colourability: NP-complete [Král' et al. 2001].
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Star
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityK4ClawDiamondFree

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-- Well-formedness of an instance: a well-formed GRAPH K-COLORABILITY instance with `K = 3`
whose graph has no `K_4`, no induced claw `K_{1,3}` and no induced diamond `K_4 - e`. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ i.2.2 = 3 ∧ (Graph i).CliqueFree 4 ∧
    ¬ (SimpleGraph.starGraph (0 : Fin 4)).IsIndContained (Graph i) ∧
    ¬ ((⊤ : SimpleGraph (Fin 4)).deleteEdges {s(0, 1)}).IsIndContained (Graph i)

open Classical in
/-- 3-COLORABILITY OF (K4, CLAW, DIAMOND)-FREE GRAPHS as a decision problem over bitstrings. -/
noncomputable def threeColorabilityK4ClawDiamondFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityK4ClawDiamondFree
