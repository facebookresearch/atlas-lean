/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRAPH MINOR TESTING: definitions

Source:
J. Matoušek and R. Thomas, "On the complexity of finding iso- and other morphisms for partial
k-trees", Discrete Mathematics 108 (1992), 343-364, doi:10.1016/0012-365X(92)90687-B (minor
containment is NP-complete, even for trees of bounded diameter);
T. Gima, S. Kumabe, K. Kurita, Y. Okada and Y. Otachi, "Dichotomies for tree minor containment
with structural parameters", in *WALCOM: Algorithms and Computation*, Lecture Notes in Computer
Science 14549, Springer (2024), 392-405, doi:10.1007/978-981-97-0566-5_28 (Section 1.2 records
the result of Matoušek and Thomas; arXiv:2311.03225).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.Graph.GraphMinor

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GraphMinorTesting

/-- An instance: the vertex count and edge list of `G`, then the vertex count and edge list of
`H`. -/
abbrev GraphMinorTestingInstance := ℕ × List (ℕ × ℕ) × ℕ × List (ℕ × ℕ)

/-- The graph `G` as a bundled finite graph on `Fin n`. -/
def hostGraph (i : GraphMinorTestingInstance) : MetaMathlibExt.FinGraph where
  V := Fin i.1
  G := Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The graph `H` as a bundled finite graph on `Fin k`. -/
def patternGraph (i : GraphMinorTestingInstance) : MetaMathlibExt.FinGraph where
  V := Fin i.2.2.1
  G := Cslib.Complexity.Karp.edgeGraph i.2.2.1 i.2.2.2

/-- Well-formedness of an instance: both edge lists are simple undirected edge lists on their
vertex sets (no duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : GraphMinorTestingInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (i.2.2.2.Nodup ∧ ∀ e ∈ i.2.2.2, e.1 < i.2.2.1 ∧ e.2 < i.2.2.1 ∧ e.1 ≠ e.2 ∧
      (e.2, e.1) ∉ i.2.2.2)

/-- `H` is a minor of `G`. -/
def GraphMinorTestingFeasible (i : GraphMinorTestingInstance) : Prop :=
  MetaMathlibExt.IsMinor (patternGraph i) (hostGraph i)

open Classical in
/-- GRAPH MINOR TESTING as a decision problem over bitstrings. -/
noncomputable def graphMinorTestingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphMinorTestingInstance) x with
  | some i => decide (WellFormed i ∧ GraphMinorTestingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GraphMinorTesting
