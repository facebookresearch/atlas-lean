/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TREE MINOR CONTAINMENT: definitions

Source:
J. Matoušek and R. Thomas, "On the complexity of finding iso- and other morphisms for partial
k-trees", Discrete Mathematics 108 (1992), 343-364, doi:10.1016/0012-365X(92)90687-B (minor
containment is NP-complete even when both graphs are trees of bounded diameter);
T. Gima, S. Kumabe, K. Kurita, Y. Okada and Y. Otachi, "Dichotomies for tree minor containment
with structural parameters", in *WALCOM: Algorithms and Computation*, Lecture Notes in Computer
Science 14549, Springer (2024), 392-405, doi:10.1007/978-981-97-0566-5_28 (arXiv:2311.03225,
Section 1, records the result of Matoušek and Thomas);
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 8 (1987), 285-303,
doi:10.1016/0196-6774(87)90043-5, Section 1 (MINOR CONTAINMENT "remains NP-complete" when both
graphs are trees, citing P. D. Seymour and P. W. Shor, private communications (1987)).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import CSLibExt.Complexity.NPComplete.GraphMinorTestingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TreeMinorContainment

open GraphMinorTesting
  (GraphMinorTestingInstance hostGraph patternGraph GraphMinorTestingFeasible)

/-- Well-formedness of an instance: a well-formed GRAPH MINOR TESTING instance (two simple edge
lists) in which both `G` and `H` are trees. -/
def WellFormed (i : GraphMinorTestingInstance) : Prop :=
  GraphMinorTesting.WellFormed i ∧ (hostGraph i).G.IsTree ∧ (patternGraph i).G.IsTree

open Classical in
/-- TREE MINOR CONTAINMENT as a decision problem over bitstrings. -/
noncomputable def treeMinorContainmentDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphMinorTestingInstance) x with
  | some i => decide (WellFormed i ∧ GraphMinorTestingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TreeMinorContainment
