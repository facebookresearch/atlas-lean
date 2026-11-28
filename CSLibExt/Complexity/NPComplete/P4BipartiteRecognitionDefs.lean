/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# P_4-BIPARTITE GRAPH RECOGNITION: definitions

Source:
C. T. Hoàng and V. B. Le, "P₄-free colorings and P₄-bipartite graphs", Discrete Mathematics and
Theoretical Computer Science 4 (2001), 109-122, doi:10.46298/dmtcs.272 (Lemma 1);
D. Achlioptas, "The complexity of G-free colourability", Discrete Mathematics 165/166 (1997),
21-30, doi:10.1016/S0012-365X(97)84217-3;
ISGCI (https://www.graphclasses.org/classes/gc_5.html), problem "Recognition" on
`P_4`-bipartite graphs: NP-complete.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ThreeColorabilityP4BipartiteDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.P4BipartiteRecognition

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev P4BipartiteRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : P4BipartiteRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : P4BipartiteRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- The graph of the instance is `P_4`-bipartite. -/
def P4BipartiteRecognitionFeasible (i : P4BipartiteRecognitionInstance) : Prop :=
  ThreeColorabilityP4Bipartite.IsP4Bipartite (Graph i)

open Classical in
/-- P_4-BIPARTITE GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def p4BipartiteRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := P4BipartiteRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ P4BipartiteRecognitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.P4BipartiteRecognition
