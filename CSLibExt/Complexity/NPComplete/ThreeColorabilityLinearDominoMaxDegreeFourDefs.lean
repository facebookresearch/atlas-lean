/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-COLORABILITY OF LINEAR DOMINO GRAPHS OF MAXIMUM DEGREE 4: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY;
Yu. Metelsky and R. Tyshkevich, "Line graphs of Helly hypergraphs", SIAM Journal on Discrete
Mathematics 16 (2003), 438-448, doi:10.1137/S089548019936521X;
D. Král', J. Kratochvíl, Zs. Tuza and G. J. Woeginger, "Complexity of coloring graphs without
forbidden induced subgraphs", Graph-Theoretic Concepts in Computer Science (WG 2001), Lecture
Notes in Computer Science 2204 (2001), 254-262, doi:10.1007/3-540-45477-2_23;
ISGCI (Information System on Graph Classes and their Inclusions), class linear domino ∩ maximum
degree 4 (gc_718), problem 3-Colourability: NP-complete [Metelsky and Tyshkevich 2003], and
NP-complete on `(K_4, claw, diamond)`-free graphs [Král' et al. 2001].
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Star
public import Mathlib.Data.Set.Card
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityLinearDominoMaxDegreeFour

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-- Well-formedness of an instance: a well-formed GRAPH K-COLORABILITY instance with `K = 3`
whose graph is linear domino (no induced claw `K_{1,3}` and no induced diamond `K_4 - e`) and has
maximum degree at most 4. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ i.2.2 = 3 ∧
    ¬ (SimpleGraph.starGraph (0 : Fin 4)).IsIndContained (Graph i) ∧
    ¬ ((⊤ : SimpleGraph (Fin 4)).deleteEdges {s(0, 1)}).IsIndContained (Graph i) ∧
    ∀ v : Fin i.1, ((Graph i).neighborSet v).ncard ≤ 4

open Classical in
/-- 3-COLORABILITY OF LINEAR DOMINO GRAPHS OF MAXIMUM DEGREE 4 as a decision problem over
bitstrings. -/
noncomputable def threeColorabilityLinearDominoMaxDegreeFourDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityLinearDominoMaxDegreeFour
