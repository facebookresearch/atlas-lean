/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROOTED TREE ARRANGEMENT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT45] ROOTED TREE
ARRANGEMENT (transformation from OPTIMAL LINEAR ARRANGEMENT);
F. Gavril, "Some NP-complete problems on graphs", Proceedings of the 11th
Conference on Information Sciences and Systems, Johns Hopkins University,
Baltimore (1977), 91-95.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RootedTreeArrangement

/-!
# ROOTED TREE ARRANGEMENT is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K`.
QUESTION: is there a rooted tree `T = (U, F)`, with `|U| = |V|`, and a one-to-one function
`f : V → U` such that for every edge `{u, v} ∈ E` there is a simple path from the root that
includes both `f(u)` and `f(v)`, and such that, if `d(x, y)` is the number of edges on the path
from `x` to `y` in `T`, then `∑_{{u, v} ∈ E} d(f(u), f(v)) ≤ K`?

The tree is a Mathlib `SimpleGraph.IsTree` on `U = Fin |V|` (any tree on a set of size `|V|`
is isomorphic to one on `Fin |V|`) with a chosen root `r`. A simple path from the root is a
`SimpleGraph.Walk` from `r` that `IsPath`. In a tree the path between two vertices is unique,
so `d(x, y)` is `T.dist x y`. The sum runs over Mathlib's edge set of `G`, each edge `{u, v}`
contributing `d(f(u), f(v))` (well defined because `dist` is symmetric). A rooted tree has a
root, so the graph with no vertices is a no-instance.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, and the bound `K`. -/
abbrev RootedTreeArrangementInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : RootedTreeArrangementInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and `K` is
positive. -/
def WellFormed (i : RootedTreeArrangementInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2

/-- The cost `∑_{{u, v} ∈ E} d(f(u), f(v))` of placing the vertices of `G` on the tree `T`
by `f`, with `d = T.dist`. -/
noncomputable def arrangementCost {n : ℕ} (G T : SimpleGraph (Fin n)) (f : Fin n → Fin n) : ℕ :=
  ∑ᶠ e ∈ G.edgeSet, Sym2.lift ⟨fun a b => T.dist (f a) (f b), fun _ _ => SimpleGraph.dist_comm⟩ e

/-- A tree `T` on `Fin n` with root `r` and a one-to-one `f` such that the images of the ends
of every edge lie on one simple path from `r`, and the total tree distance is at most `K`. -/
def RootedTreeArrangementFeasible (i : RootedTreeArrangementInstance) : Prop :=
  ∃ T : SimpleGraph (Fin i.1), T.IsTree ∧ ∃ r : Fin i.1, ∃ f : Fin i.1 → Fin i.1,
    Function.Injective f ∧
      (∀ u v, (Graph i).Adj u v →
        ∃ x, ∃ p : T.Walk r x, p.IsPath ∧ f u ∈ p.support ∧ f v ∈ p.support) ∧
      arrangementCost (Graph i) T f ≤ i.2.2

open Classical in
/-- ROOTED TREE ARRANGEMENT as a decision problem over bitstrings. -/
noncomputable def rootedTreeArrangementDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RootedTreeArrangementInstance) x with
  | some i => decide (WellFormed i ∧ RootedTreeArrangementFeasible i)
  | none => false

/-- **ROOTED TREE ARRANGEMENT is NP-complete.** Source: Garey and Johnson (1979), [GT45];
Gavril (1977). -/
public theorem_wanted rootedTreeArrangement_npComplete :
    rootedTreeArrangementDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rootedTreeArrangementDec

end MetaMathlibExt.Complexity.NPComplete.RootedTreeArrangement
