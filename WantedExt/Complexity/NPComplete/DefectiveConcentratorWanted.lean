/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DEFECTIVE CONCENTRATOR is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6(1)
(1985), 145-159, doi:10.1016/0196-6774(85)90025-2, problem [8] DEFECTIVE SUPERCONCENTRATOR,
comment ("Also NP-complete are the problems of identifying defective ... 'concentrators'");
M. Blum, R. M. Karp, O. Vornberger, C. H. Papadimitriou and M. Yannakakis, "The complexity of
testing whether a graph is a superconcentrator", Information Processing Letters 13(4-5) (1981),
164-167, doi:10.1016/0020-0190(81)90050-8.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Card
public import Mathlib.Logic.Relation
public import WantedExt.Complexity.NPComplete.DefectiveSuperconcentratorWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DefectiveConcentrator

open MetaMathlibExt.Complexity.NPComplete.DefectiveSuperconcentrator
  (DefectiveSuperconcentratorInstance)

/-!
# DEFECTIVE CONCENTRATOR is NP-complete

INSTANCE: an acyclic directed graph `G = (V, A)` and disjoint sets `I, O ⊆ V` of "input" and
"output" vertices with `|O| ≤ |I|`.
QUESTION: is it the case that `G` is not a concentrator? (It would be one if, for every subset
`S ⊆ I` with `|S| = |O|`, there are `|S|` vertex-disjoint paths from `S` to `O`.)

Johnson's column defines a concentrator this way and records, citing Blum, Karp, Vornberger,
Papadimitriou and Yannakakis, that identifying defective concentrators is NP-complete, even if
`G` has no path longer than two arcs (and polynomial if it has no path longer than one arc). As
for the standard `(n, m)`-concentrator, the instance has at least as many inputs as outputs
(`|O| ≤ |I|`); then the condition is equivalent to routing every input set of size at most
`|O|`.

The instance and the representation are those of DEFECTIVE SUPERCONCENTRATOR
(`WantedExt.Complexity.NPComplete.DefectiveSuperconcentratorWanted`): vertices `0, …, n - 1`,
the arcs a list of ordered pairs without repetitions or loops, `I` and `O` lists without
repetitions, and acyclicity as "no vertex reaches itself by a nonempty directed path"
(`Relation.TransGen` of the arc relation). `WellFormed` is that problem's well-formedness with
its condition `|I| = |O|` relaxed to `|O| ≤ |I|`. A path from `S` to `O` is a directed path, in
the sense of `DirectedTwoDisjointConnectingPaths.IsDirectedPath` (pairwise distinct vertices, an
arc from each vertex to the next), that starts at a vertex of `S` and ends at a vertex of `O`;
paths are vertex-disjoint when their vertex lists are disjoint. Membership in NP follows from the
max-flow min-cut theorem, as for DEFECTIVE SUPERCONCENTRATOR (a set `S` together with a vertex
cut of size below `|S|` is a certificate).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **DEFECTIVE CONCENTRATOR is NP-complete.** Source: Johnson (1985), NP-completeness column;
Blum, Karp, Vornberger, Papadimitriou and Yannakakis (1981). -/
public theorem_wanted defectiveConcentrator_npComplete :
    defectiveConcentratorDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L defectiveConcentratorDec

end MetaMathlibExt.Complexity.NPComplete.DefectiveConcentrator
