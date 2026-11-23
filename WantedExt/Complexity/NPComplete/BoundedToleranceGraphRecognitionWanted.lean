/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOUNDED TOLERANCE GRAPH RECOGNITION is NP-complete

Source:
G. B. Mertzios, I. Sau and S. Zaks, "The recognition of tolerance and bounded tolerance graphs",
SIAM Journal on Computing 40 (2011), 1234-1257, doi:10.1137/090780328 (arXiv:1001.3251;
Section 1: the definitions of tolerance and bounded tolerance graphs used below, and "both
recognition problems are NP-complete", membership in NP citing Hayward and Shamir).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ToleranceGraphRecognitionWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoundedToleranceGraphRecognition

open MetaMathlibExt.Complexity.NPComplete.ToleranceGraphRecognition
  (ToleranceGraphRecognitionInstance Graph IsToleranceRepresentation)

/-!
# BOUNDED TOLERANCE GRAPH RECOGNITION is NP-complete

INSTANCE: a graph `G = (V, E)`. QUESTION: is `G` a bounded tolerance graph?

Mertzios, Sau and Zaks (Section 1): `G` is a tolerance graph if there are closed intervals `I_i`
on the real line and positive numbers `t_i` such that `v_i v_j ∈ E` if and only if
`|I_i ∩ I_j| ≥ min{t_i, t_j}`; "If `G` has a tolerance representation `⟨I, t⟩`, such that
`t_i ≤ |I_i|` for every `i = 1, 2, …, n`, then `G` is called a bounded tolerance graph". They
prove that recognizing bounded tolerance graphs is NP-complete.

The instance, the graph, the well-formedness condition and the tolerance representation are
those of the merged `ToleranceGraphRecognitionWanted`, reused unchanged: an edge list on `Fin n`
(`ToleranceGraphRecognitionInstance`, `ToleranceGraphRecognition.Graph`,
`ToleranceGraphRecognition.WellFormed`), and `ToleranceGraphRecognition.IsToleranceRepresentation`
(vertex `v` gets the closed interval `[l v, r v]`, `l v ≤ r v`, and the tolerance `t v > 0`; two
distinct vertices are adjacent exactly when the length of the intersection of their intervals is
at least the smaller tolerance). The question adds the boundedness condition `t v ≤ r v - l v`
(`r v - l v` is the length `|I_v|` of `[l v, r v]`) for every vertex.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The graph of the instance is a bounded tolerance graph: it has a tolerance representation
in which every tolerance is at most the length of its vertex's interval. -/
def BoundedToleranceGraphRecognitionFeasible (i : ToleranceGraphRecognitionInstance) : Prop :=
  ∃ l r t : Fin i.1 → ℝ, IsToleranceRepresentation (Graph i) l r t ∧ ∀ v, t v ≤ r v - l v

open Classical in
/-- BOUNDED TOLERANCE GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def boundedToleranceGraphRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ToleranceGraphRecognitionInstance) x with
  | some i =>
    decide (ToleranceGraphRecognition.WellFormed i ∧ BoundedToleranceGraphRecognitionFeasible i)
  | none => false

/-- **BOUNDED TOLERANCE GRAPH RECOGNITION is NP-complete.** Source: Mertzios, Sau and Zaks
(2011). -/
public theorem_wanted boundedToleranceGraphRecognition_npComplete :
    boundedToleranceGraphRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L boundedToleranceGraphRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.BoundedToleranceGraphRecognition
