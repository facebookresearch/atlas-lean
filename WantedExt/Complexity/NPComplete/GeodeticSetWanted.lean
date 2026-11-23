/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GEODETIC SET is NP-complete

Source:
M. Atici, "Computational complexity of geodetic set", International Journal of Computer
Mathematics 79(5) (2002), 587-591, doi:10.1080/00207160210954.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeodeticSet

/-!
# GEODETIC SET is NP-complete

INSTANCE: a connected graph `G = (V, E)` (finite, simple, undirected) and a positive integer
`K`.
QUESTION: is there a set `S ⊆ V` with `|S| ≤ K` such that every vertex lies on some shortest
path between two vertices of `S`?

A vertex `x` lies on a shortest `u`-`v` path when some walk from `u` to `v` of length
`G.dist u v` (Mathlib's distance; the graph is connected) passes through `x`; a shortest walk is
a path. The two vertices of `S` may coincide, so every vertex of `S` is covered by its own
trivial path.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), edge list, and the bound `K`. -/
abbrev GeodeticSetInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : GeodeticSetInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph (no duplicate edges
in either orientation, no self-loops, endpoints in range), the graph is connected, and
`0 < K`. -/
def WellFormed (i : GeodeticSetInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (Graph i).Connected ∧ 0 < i.2.2

/-- Some set `S` of at most `K` vertices is geodetic: every vertex `x` lies on a shortest walk
between two vertices `u, v ∈ S`. -/
def GeodeticSetFeasible (i : GeodeticSetInstance) : Prop :=
  ∃ S : Finset (Fin i.1), S.card ≤ i.2.2 ∧ ∀ x, ∃ u ∈ S, ∃ v ∈ S,
    ∃ p : (Graph i).Walk u v, p.length = (Graph i).dist u v ∧ x ∈ p.support

open Classical in
/-- GEODETIC SET as a decision problem over bitstrings. -/
noncomputable def geodeticSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GeodeticSetInstance) x with
  | some i => decide (WellFormed i ∧ GeodeticSetFeasible i)
  | none => false

/-- **GEODETIC SET is NP-complete.** Source: Atici (2002). -/
public theorem_wanted geodeticSet_npComplete :
    geodeticSetDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L geodeticSetDec

end MetaMathlibExt.Complexity.NPComplete.GeodeticSet
