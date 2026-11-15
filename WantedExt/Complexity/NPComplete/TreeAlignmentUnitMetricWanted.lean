/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TREE ALIGNMENT (given phylogeny, unit metric) is NP-complete

Source:
I. Elias, "Settling the intractability of multiple alignment", Journal of Computational Biology
13(7) (2006), 1323-1339, doi:10.1089/cmb.2006.13.1323.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Algorithms.Lean.DynamicProgramming.EditDistance.Algorithm
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TreeAlignmentUnitMetric

/-!
# TREE ALIGNMENT (given phylogeny, unit metric) is NP-complete

INSTANCE: a finite alphabet `Σ`, a rooted binary tree `T` (the phylogeny) whose `k` leaves are
labelled by strings over `Σ`, and an integer `K`. QUESTION: can the `k - 1` internal vertices
of `T` be labelled by strings over `Σ` so that the sum, over the edges `{u, v}` of `T`, of the
edit distance between the labels of `u` and `v` is at most `K`?

The edit distance is the unit metric: the cost of an optimal pairwise alignment when a
substitution of distinct letters, an insertion and a deletion each cost `1`, that is, CSLib's
unit-cost Levenshtein distance `(Cslib.Algorithms.Lean.editDistance x y).ret.distance`. Elias
(2006) proves TREE ALIGNMENT for a given phylogeny NP-hard for every metric over binary or
larger alphabets, in particular for the unit metric. Membership in NP: in an optimal labelling,
a column of the induced multiple alignment in which every leaf has a gap can be deleted without
raising the cost, so some optimal labelling has internal labels no longer than the total length
of the leaf labels.

Representation: the alphabet is `Σ = {0, ..., |Σ| - 1}` with `|Σ| ≥ 2`, and strings are lists
of letters. The tree has vertices `0, ..., n - 1` with `n = p.length + 1`, root `0`, and is
given by a parent list `p`: vertex `v + 1` is a child of vertex `p[v] ≤ v`. Every rooted tree
has such a list (number its vertices in breadth-first order from the root), and every such list
is a rooted tree. The phylogeny is binary, as in Elias's formulation (`k` leaves and `k - 1`
internal labels): every vertex has no child (a leaf) or exactly two children. The leaf
labelling is a list of (vertex, string) pairs naming every leaf exactly once.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the alphabet size `|Σ|`, the parent list of the tree, the leaf labels as
(vertex, string) pairs, and the bound `K`. -/
abbrev TreeAlignmentUnitMetricInstance := ℕ × List ℕ × List (ℕ × List ℕ) × ℕ

/-- The number of vertices `n = p.length + 1`. -/
abbrev numVertices (i : TreeAlignmentUnitMetricInstance) : ℕ := i.2.1.length + 1

/-- The number of children of vertex `v`. -/
def children (i : TreeAlignmentUnitMetricInstance) (v : ℕ) : ℕ := i.2.1.count v

/-- Well-formedness of an instance: the alphabet has at least two letters (the source's binary or
larger alphabets), the parent of vertex `v + 1` is at most `v` (so the parent list is a rooted
tree), every vertex has zero or two children (a binary phylogeny), the leaf
labels name distinct vertices, a vertex is named iff it is a leaf (has no children), and the
labels are strings over `Σ`. -/
def WellFormed (i : TreeAlignmentUnitMetricInstance) : Prop :=
  2 ≤ i.1 ∧ (∀ v : Fin i.2.1.length, i.2.1.get v ≤ (v : ℕ)) ∧
    (∀ v < numVertices i, children i v = 0 ∨ children i v = 2) ∧
    (i.2.2.1.map Prod.fst).Nodup ∧
    (∀ v < numVertices i, v ∈ i.2.2.1.map Prod.fst ↔ children i v = 0) ∧
    (∀ q ∈ i.2.2.1, q.1 < numVertices i ∧ ∀ a ∈ q.2, a < i.1)

/-- The edit (Levenshtein) distance. -/
def editDist (x y : List ℕ) : ℕ := (Cslib.Algorithms.Lean.editDistance x y).ret.distance

/-- The cost of a labelling `lab` of the vertices: the sum over the edges `{v + 1, p[v]}` of
the edit distance between the labels of their ends. -/
def cost (i : TreeAlignmentUnitMetricInstance) (lab : ℕ → List ℕ) : ℕ :=
  ((List.range i.2.1.length).map fun v => editDist (lab (v + 1)) (lab (i.2.1.getD v 0))).sum

/-- Some labelling of the vertices by strings over `Σ` that agrees with the given labels on the
leaves has cost at most `K`. -/
def TreeAlignmentUnitMetricFeasible (i : TreeAlignmentUnitMetricInstance) : Prop :=
  ∃ lab : ℕ → List ℕ, (∀ v < numVertices i, ∀ a ∈ lab v, a < i.1) ∧
    (∀ q ∈ i.2.2.1, lab q.1 = q.2) ∧ cost i lab ≤ i.2.2.2

open Classical in
/-- TREE ALIGNMENT (given phylogeny, unit metric) as a decision problem over bitstrings. -/
noncomputable def treeAlignmentUnitMetricDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TreeAlignmentUnitMetricInstance) x with
  | some i => decide (WellFormed i ∧ TreeAlignmentUnitMetricFeasible i)
  | none => false

/-- **TREE ALIGNMENT (given phylogeny, unit metric) is NP-complete.** Source: Elias (2006). -/
public theorem_wanted treeAlignmentUnitMetric_npComplete :
    treeAlignmentUnitMetricDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L treeAlignmentUnitMetricDec

end MetaMathlibExt.Complexity.NPComplete.TreeAlignmentUnitMetric
