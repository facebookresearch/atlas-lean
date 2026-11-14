/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CUBICAL GRAPH RECOGNITION is NP-complete

Source:
F. Afrati, C. H. Papadimitriou and G. Papageorgiou, "The complexity of cubical graphs",
Information and Control 66 (1985), 53-60, doi:10.1016/S0019-9958(85)80012-7.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.HypercubeExtremal

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CubicalGraphRecognition

/-!
# CUBICAL GRAPH RECOGNITION is NP-complete

Following Afrati, Papadimitriou and Papageorgiou (1985), a graph is *cubical* if it is a
subgraph of a hypercube. INSTANCE: a graph `G = (V, E)`. QUESTION: is `G` cubical, that is, is
`G` a subgraph of the hypercube `Q_d` for some `d`?

`Q_d` is the shared `SimpleGraph.hypercubeGraph d` (vertices `Fin d → Bool`, adjacent when they
differ in exactly one coordinate). "Subgraph", not necessarily induced, is Mathlib's
`SimpleGraph.IsContained` (`G ⊑ Q_d`): an injective map of the vertices that sends every edge
of `G` to an edge of `Q_d`. The dimension `d` is existentially quantified and is not part of the
instance.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev CubicalGraphRecognitionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CubicalGraphRecognitionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : CubicalGraphRecognitionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- The graph is cubical: it is contained in the hypercube `Q_d` for some dimension `d`. -/
def CubicalGraphRecognitionFeasible (i : CubicalGraphRecognitionInstance) : Prop :=
  ∃ d : ℕ, (Graph i).IsContained (SimpleGraph.hypercubeGraph d)

open Classical in
/-- CUBICAL GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def cubicalGraphRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CubicalGraphRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ CubicalGraphRecognitionFeasible i)
  | none => false

/-- **CUBICAL GRAPH RECOGNITION is NP-complete.** Source: Afrati, Papadimitriou and
Papageorgiou (1985). -/
public theorem_wanted cubicalGraphRecognition_npComplete :
    cubicalGraphRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cubicalGraphRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.CubicalGraphRecognition
