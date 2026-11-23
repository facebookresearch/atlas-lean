/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BRANCHWIDTH is NP-complete

Source:
P. D. Seymour and R. Thomas, "Call routing and the ratcatcher", Combinatorica 14 (1994),
217-241, doi:10.1007/BF01215352 (branchwidth "is NP-hard for general graphs"; definitions in
Section 1, (1.1)).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Branchwidth

/-!
# BRANCHWIDTH is NP-complete

INSTANCE: a graph `G = (V, E)` and an integer `K`. QUESTION: is the branchwidth of `G` at most
`K`?

Following Seymour and Thomas: a branch decomposition of `G` is a tree `T` in which every vertex
has valency `1` or `3`, with a bijection `τ` from `E` onto the set of leaves of `T`. Removing
an edge `xy` of `T` splits `T` into two components; the edges of `G` whose leaves lie in the
component of `x` form a set `A`, and `∂(A)` is the set of vertices of `G` incident with an edge
in `A` and with an edge in `E - A`. The width of the decomposition is the maximum of `|∂(A)|`
over the edges of `T`, and the branchwidth of `G` is the minimum width of a branch
decomposition, "or zero, if `|E(G)| ≤ 1`" (then `G` has no branch decomposition). So the
branchwidth is at most `K` exactly when `|E| ≤ 1` or some branch decomposition has every
`|∂(A)| ≤ K`.

The tree is a Mathlib `SimpleGraph` on `Fin m` (`SimpleGraph.IsTree`, valencies
`SimpleGraph.degree`); the component of `x` after removing `xy` is the set of vertices
reachable from `x` in `T.deleteEdges {s(x, y)}`. The edges of `G` are the entries of the edge
list, indexed by `Fin es.length`; under `WellFormed` there are no duplicate edges in either
orientation, so the entries are exactly `E`. `K` ranges over `ℕ`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), edge list, bound `K`. -/
abbrev BranchwidthInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: the edge list describes a simple graph on `0, …, n - 1` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : BranchwidthInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

open Classical in
/-- `(T, τ)` is a branch decomposition of the edge list `es` (on vertices `0, …, n - 1`) of
width at most `K`: `T` is a tree whose vertices all have valency `1` or `3`, `τ` is a bijection
from the edges onto the leaves of `T`, and for every edge `xy` of `T`, with `A` the edges whose
leaves are reachable from `x` once `xy` is removed, at most `K` vertices are incident both with
an edge in `A` and with an edge not in `A`. -/
def IsBranchDecompositionOfWidth (n : ℕ) (es : List (ℕ × ℕ)) (K : ℕ) {m : ℕ}
    (T : SimpleGraph (Fin m)) (τ : Fin es.length → Fin m) : Prop :=
  T.IsTree ∧ (∀ x, T.degree x = 1 ∨ T.degree x = 3) ∧ Function.Injective τ ∧
    (∀ x, T.degree x = 1 ↔ x ∈ Set.range τ) ∧
    ∀ x y, T.Adj x y →
      ((Finset.range n).filter fun v =>
        (∃ j, (T.deleteEdges {s(x, y)}).Reachable x (τ j) ∧
          (v = (es.get j).1 ∨ v = (es.get j).2)) ∧
        (∃ j, ¬ (T.deleteEdges {s(x, y)}).Reachable x (τ j) ∧
          (v = (es.get j).1 ∨ v = (es.get j).2))).card ≤ K

/-- The branchwidth is at most `K`: the graph has at most one edge, or some branch decomposition
has width at most `K`. -/
def BranchwidthFeasible (i : BranchwidthInstance) : Prop :=
  i.2.1.length ≤ 1 ∨ ∃ (m : ℕ) (T : SimpleGraph (Fin m)) (τ : Fin i.2.1.length → Fin m),
    IsBranchDecompositionOfWidth i.1 i.2.1 i.2.2 T τ

open Classical in
/-- BRANCHWIDTH as a decision problem over bitstrings. -/
noncomputable def branchwidthDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BranchwidthInstance) x with
  | some i => decide (WellFormed i ∧ BranchwidthFeasible i)
  | none => false

/-- **BRANCHWIDTH is NP-complete.** Source: Seymour and Thomas (1994). -/
public theorem_wanted branchwidth_npComplete :
    branchwidthDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L branchwidthDec

end MetaMathlibExt.Complexity.NPComplete.Branchwidth
