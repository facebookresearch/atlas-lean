/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC NUMBER OF H-FREE GRAPHS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY (CHROMATIC
NUMBER), the problem restricted here;
D. Král', J. Kratochvíl, Zs. Tuza and G. J. Woeginger, "Complexity of coloring graphs without
forbidden induced subgraphs", Graph-Theoretic Concepts in Computer Science (WG 2001), Lecture
Notes in Computer Science 2204 (2001), 254-262, doi:10.1007/3-540-45477-2_23.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChromaticNumberHFreeGraphs

/-- Well-formedness of an instance for the forbidden graph `H`: it is a well-formed GRAPH
COLORING instance (a simple graph given by an edge list), `K` is positive, and `H` is not an
induced subgraph of its graph. -/
def WellFormed {h : ℕ} (H : SimpleGraph (Fin h)) (i : GraphColoring.GraphColoringInstance) :
    Prop :=
  GraphColoring.WellFormed i ∧ 0 < i.2.2 ∧ ¬ H.IsIndContained (GraphColoring.Graph i)

open Classical in
/-- CHROMATIC NUMBER OF `H`-FREE GRAPHS as a decision problem over bitstrings. -/
noncomputable def chromaticNumberHFreeGraphsDec {h : ℕ} (H : SimpleGraph (Fin h)) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphColoring.GraphColoringInstance) x with
  | some i => decide (WellFormed H i ∧ GraphColoring.GraphColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ChromaticNumberHFreeGraphs
