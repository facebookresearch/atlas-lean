/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE on unit 3-circular track graphs: definitions

Source:
ISGCI (Information System on Graph Classes and their Inclusions), class "unit 3-circular track"
(gc_1089, https://www.graphclasses.org/classes/gc_1089.html), problem Clique: NP-complete, citing
M. C. Francis, D. Gonçalves and P. Ochem, "The maximum clique problem in multiple interval
graphs", Algorithmica 71(4) (2015), 812-836, doi:10.1007/s00453-013-9828-6 (Section 1: t-circular
track graphs and their unit subclass; Theorem 10: "MAXIMUM CLIQUE is NP-complete for unit
2-interval and unit 3-track graphs"; conference version in WG 2012, Lecture Notes in Computer
Science 7551, 57-68; arXiv:1201.0043);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT19] CLIQUE.
-/
module

public import Mathlib.Topology.Instances.AddCircle.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.CliqueUnitThreeTrackDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CliqueUnitThreeCircularTrack

open MetaMathlibExt.Complexity.NPComplete.CliqueUnitThreeTrack
  (CliqueUnitThreeTrackInstance Graph CliqueUnitThreeTrackFeasible)

/-- `H` is a unit `d`-circular track graph: for each track `j : Fin d` there is a circle
`AddCircle (c j)` with `c j > 0`, each vertex `v` is assigned on it the closed unit arc from the
point `l v j` to `l v j + 1` (the image of `[l v j, l v j + 1]`), and two distinct vertices are
adjacent in `H` exactly when their arcs on some track meet. -/
def IsUnitCircularTrackGraph (d : ℕ) {n : ℕ} (H : SimpleGraph (Fin n)) : Prop :=
  ∃ (c : Fin d → ℝ) (l : Fin n → Fin d → ℝ), (∀ j, 0 < c j) ∧
    ∀ u v, u ≠ v → (H.Adj u v ↔ ∃ j,
      (((↑) : ℝ → AddCircle (c j)) '' Set.Icc (l u j) (l u j + 1) ∩
        ((↑) : ℝ → AddCircle (c j)) '' Set.Icc (l v j) (l v j + 1)).Nonempty)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), the graph is a unit
3-circular track graph, and `0 < K ≤ n`. -/
def WellFormed (i : CliqueUnitThreeTrackInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    IsUnitCircularTrackGraph 3 (Graph i) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- CLIQUE on unit 3-circular track graphs as a decision problem over bitstrings. -/
noncomputable def cliqueUnitThreeCircularTrackDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CliqueUnitThreeTrackInstance) x with
  | some i => decide (WellFormed i ∧ CliqueUnitThreeTrackFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CliqueUnitThreeCircularTrack
