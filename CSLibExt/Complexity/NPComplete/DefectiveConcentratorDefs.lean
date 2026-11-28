/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DEFECTIVE CONCENTRATOR: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6(1)
(1985), 145-159, doi:10.1016/0196-6774(85)90025-2, problem [8] DEFECTIVE SUPERCONCENTRATOR,
comment ("Also NP-complete are the problems of identifying defective ... 'concentrators'");
M. Blum, R. M. Karp, O. Vornberger, C. H. Papadimitriou and M. Yannakakis, "The complexity of
testing whether a graph is a superconcentrator", Information Processing Letters 13(4-5) (1981),
164-167, doi:10.1016/0020-0190(81)90050-8.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Card
public import Mathlib.Logic.Relation
public import CSLibExt.Complexity.NPComplete.DefectiveSuperconcentratorDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DefectiveConcentrator

open MetaMathlibExt.Complexity.NPComplete.DefectiveSuperconcentrator
  (DefectiveSuperconcentratorInstance)

/-- Well-formedness of an instance: the arcs are distinct, loopless and between vertices; the
digraph is acyclic; `I` and `O` are lists of distinct vertices, disjoint from each other, with
`|O| ≤ |I|`. -/
def WellFormed (i : DefectiveSuperconcentratorInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2) ∧
    (∀ v : ℕ, ¬ Relation.TransGen (fun u w => (u, w) ∈ i.2.1) v v) ∧
    i.2.2.1.Nodup ∧ i.2.2.2.Nodup ∧ (∀ v ∈ i.2.2.1, v < i.1) ∧ (∀ v ∈ i.2.2.2, v < i.1) ∧
    i.2.2.1.Disjoint i.2.2.2 ∧ i.2.2.2.length ≤ i.2.2.1.length

/-- The digraph is a concentrator: for every set `S ⊆ I` with `|S| = |O|` there are `|S|`
pairwise vertex-disjoint directed paths, each from a vertex of `S` to a vertex of `O`. -/
def IsConcentrator (i : DefectiveSuperconcentratorInstance) : Prop :=
  ∀ S : Finset ℕ, S ⊆ i.2.2.1.toFinset → S.card = i.2.2.2.length →
    ∃ P : Fin S.card → List ℕ,
      (∀ j, ∃ s ∈ S, ∃ t ∈ i.2.2.2,
        DirectedTwoDisjointConnectingPaths.IsDirectedPath i.2.1 s t (P j)) ∧
        ∀ j k, j ≠ k → (P j).Disjoint (P k)

/-- The digraph is not a concentrator. -/
def DefectiveConcentratorFeasible (i : DefectiveSuperconcentratorInstance) : Prop :=
  ¬ IsConcentrator i

open Classical in
/-- DEFECTIVE CONCENTRATOR as a decision problem over bitstrings. -/
noncomputable def defectiveConcentratorDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DefectiveSuperconcentratorInstance) x with
  | some i => decide (WellFormed i ∧ DefectiveConcentratorFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DefectiveConcentrator
