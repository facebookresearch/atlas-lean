/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PURE-k-DIR GRAPH RECOGNITION is NP-complete for every fixed k ≥ 2: definitions

Source:
J. Kratochvíl and J. Matoušek, "NP-hardness results for intersection graphs",
Commentationes Mathematicae Universitatis Carolinae 30 (1989), no. 4, 761-773,
http://dml.cz/dmlcz/106799 (Section 2 definitions, Theorem 1 and Proposition 5);
J. Kratochvíl, "A special planar satisfiability problem and a consequence of its
NP-completeness", Discrete Applied Mathematics 52 (1994), 233-252,
doi:10.1016/0166-218X(94)90143-0 (the case `k = 2`);
J. Kratochvíl and J. Matoušek, "Intersection graphs of segments", Journal of Combinatorial
Theory, Series B 62 (1994), 289-315, doi:10.1006/jctb.1994.1071 (membership in NP);
ISGCI, *Information System on Graph Classes and their Inclusions*, classes PURE-2-DIR
(gc_867) and PURE-3-DIR (gc_868), problem Recognition: NP-complete.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.KDirGraphRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PureKDirGraphRecognition

open KDirGraphRecognition (KDirGraphRecognitionInstance Graph WellFormed)

/-- `H` is a PURE-`k`-DIR graph: there are slopes `s j` (`j : Fin k`) and, for each vertex `v`, a
non-degenerate closed segment from `a v` to `b v` whose slope is `s (c v)`, such that segments of
distinct vertices with the same slope are disjoint, and two distinct vertices are adjacent in `H`
exactly when their segments intersect. -/
def IsPureKDirGraph (k : ℕ) {n : ℕ} (H : SimpleGraph (Fin n)) : Prop :=
  ∃ (s : Fin k → ℝ) (a b : Fin n → ℝ × ℝ) (c : Fin n → Fin k),
    (∀ v, (a v).1 < (b v).1 ∧ (b v).2 - (a v).2 = s (c v) * ((b v).1 - (a v).1)) ∧
      (∀ u v, u ≠ v → s (c u) = s (c v) →
        SimpleGraph.Segment (a u) (b u) ∩ SimpleGraph.Segment (a v) (b v) = ∅) ∧
      ∀ u v, u ≠ v →
        (H.Adj u v ↔
          (SimpleGraph.Segment (a u) (b u) ∩ SimpleGraph.Segment (a v) (b v)).Nonempty)

/-- The graph of the instance is a PURE-`k`-DIR graph. -/
def PureKDirGraphRecognitionFeasible (k : ℕ) (i : KDirGraphRecognitionInstance) : Prop :=
  IsPureKDirGraph k (Graph i)

open Classical in
/-- PURE-k-DIR GRAPH RECOGNITION, for the fixed number of slopes `k`, as a decision problem over
bitstrings. -/
noncomputable def pureKDirGraphRecognitionDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KDirGraphRecognitionInstance) x with
  | some i => decide (WellFormed i ∧ PureKDirGraphRecognitionFeasible k i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PureKDirGraphRecognition
