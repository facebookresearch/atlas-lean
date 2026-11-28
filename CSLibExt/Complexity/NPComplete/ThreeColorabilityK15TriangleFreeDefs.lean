/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-COLORABILITY OF (K_{1,5}, TRIANGLE)-FREE GRAPHS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY;
F. Maffray and M. Preissmann, "On the NP-completeness of the k-colorability problem for
triangle-free graphs", Discrete Mathematics 162 (1996), 313-317,
doi:10.1016/S0012-365X(97)89267-9;
ISGCI (Information System on Graph Classes and their Inclusions), class `(K_{1,5}, triangle)`-free
(gc_921), problem 3-Colourability: NP-complete [Maffray and Preissmann 1996].
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Star
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityK15TriangleFree

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-- Well-formedness of an instance: a well-formed GRAPH K-COLORABILITY instance with `K = 3`
whose graph has no triangle and no induced star `K_{1,5}`. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ i.2.2 = 3 ∧ (Graph i).CliqueFree 3 ∧
    ¬ (SimpleGraph.starGraph (0 : Fin 6)).IsIndContained (Graph i)

open Classical in
/-- 3-COLORABILITY OF (K_{1,5}, TRIANGLE)-FREE GRAPHS as a decision problem over bitstrings. -/
noncomputable def threeColorabilityK15TriangleFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ThreeColorabilityK15TriangleFree
