/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT on cubic graphs: definitions

Source:
P. Berman and M. Karpinski, "On some tighter inapproximability results (extended abstract)",
Automata, Languages and Programming (ICALP 1999), LNCS 1644 (1999), 200-209,
doi:10.1007/3-540-48523-6_17 (approximating MAX CUT on 3-regular graphs within some constant
factor below 1 is NP-hard);
J. Díaz and G. B. Mertzios, "Minimum bisection is NP-hard on unit disk graphs", Information and
Computation 256 (2017), 83-92, doi:10.1016/j.ic.2017.04.010, proof of Lemma 1 ("The Max-Cut
problem is NP-hard, even when restricted to cubic graphs, i.e. to graphs G = (V, E) where
|N(u)| = 3 for every vertex u ∈ V", citing M. Yannakakis, "Node- and edge-deletion NP-complete
problems", STOC 1978, 253-264, doi:10.1145/800133.804355).
-/
module

public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MaxCutDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutCubic

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutInstance MaxCutFeasible)

open Classical in
/-- Well-formedness of an instance: a well-formed MAXIMUM CUT instance (a simple edge list on
the vertices `0, ..., n - 1`) whose graph is cubic, and `0 < K`. -/
def WellFormed (i : MaxCutInstance) : Prop :=
  MaxCut.WellFormed i ∧ (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).IsRegularOfDegree 3 ∧
    0 < i.2.2

open Classical in
/-- SIMPLE MAX CUT on cubic graphs as a decision problem over bitstrings. -/
noncomputable def simpleMaxCutCubicDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := MaxCutInstance) x with
  | some i => decide (WellFormed i ∧ MaxCutFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutCubic
