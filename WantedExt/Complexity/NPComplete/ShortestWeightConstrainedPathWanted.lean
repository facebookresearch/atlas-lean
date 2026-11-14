/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SHORTEST WEIGHT-CONSTRAINED PATH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND30] SHORTEST
WEIGHT-CONSTRAINED PATH (attributed there to N. Megiddo, 1977, private
communication; transformation from PARTITION).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShortestWeightConstrainedPath

/-!
# SHORTEST WEIGHT-CONSTRAINED PATH is NP-complete

INSTANCE: a graph `G = (V, E)`, a length `l(e) ∈ ℤ⁺` and a weight `w(e) ∈ ℤ⁺` for each
`e ∈ E`, specified vertices `s, t ∈ V`, and positive integers `K, W`.
QUESTION: is there a simple path in `G` from `s` to `t` with total weight `W` or less and total
length `K` or less?

A simple path is a Mathlib `SimpleGraph.Walk` that `IsPath`; its total length (weight) is the
sum of `l` (`w`) over the edges it traverses, read from the edge list. Numbers use the binary
encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), the edges as `(u, v, l, w)` (endpoints,
length, weight), `s`, `t`, `K`, `W`. -/
abbrev ShortestWeightConstrainedPathInstance := ℕ × List (ℕ × ℕ × ℕ × ℕ) × ℕ × ℕ × ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : ShortestWeightConstrainedPathInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (i.2.1.map fun e => (e.1, e.2.1))

/-- The `(length, weight)` of the listed edge joining `a` and `b` (in either orientation);
`(0, 0)` if there is none. Under `WellFormed` at most one listed edge joins them. -/
def edgeData (i : ShortestWeightConstrainedPathInstance) (a b : ℕ) : ℕ × ℕ :=
  ((i.2.1.find? fun e => decide ((e.1, e.2.1) = (a, b) ∨ (e.1, e.2.1) = (b, a))).map
    fun e => e.2.2).getD (0, 0)

/-- Well-formedness of an instance: the edges join distinct in-range vertices, no two listed
edges join the same pair of vertices (in either orientation), every length and weight is
positive, `s, t ∈ V`, and `K, W` are positive. -/
def WellFormed (i : ShortestWeightConstrainedPathInstance) : Prop :=
  (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧ 0 < e.2.2.1 ∧ 0 < e.2.2.2) ∧
    (i.2.1.map fun e => (e.1, e.2.1)).Nodup ∧
    (∀ e ∈ i.2.1, (e.2.1, e.1) ∉ i.2.1.map fun e => (e.1, e.2.1)) ∧
    i.2.2.1 < i.1 ∧ i.2.2.2.1 < i.1 ∧ 0 < i.2.2.2.2.1 ∧ 0 < i.2.2.2.2.2

/-- A simple path from `s` to `t` whose total weight is at most `W` and whose total length is
at most `K`. -/
def ShortestWeightConstrainedPathFeasible (i : ShortestWeightConstrainedPathInstance) : Prop :=
  ∃ (hs : i.2.2.1 < i.1) (ht : i.2.2.2.1 < i.1),
    ∃ p : (Graph i).Walk ⟨i.2.2.1, hs⟩ ⟨i.2.2.2.1, ht⟩, p.IsPath ∧
      (p.darts.map fun d => (edgeData i d.fst d.snd).2).sum ≤ i.2.2.2.2.2 ∧
      (p.darts.map fun d => (edgeData i d.fst d.snd).1).sum ≤ i.2.2.2.2.1

open Classical in
/-- SHORTEST WEIGHT-CONSTRAINED PATH as a decision problem over bitstrings. -/
noncomputable def shortestWeightConstrainedPathDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ShortestWeightConstrainedPathInstance) x with
  | some i => decide (WellFormed i ∧ ShortestWeightConstrainedPathFeasible i)
  | none => false

/-- **SHORTEST WEIGHT-CONSTRAINED PATH is NP-complete.** Source: Garey and Johnson (1979),
[ND30] (Megiddo, 1977, private communication). -/
public theorem_wanted shortestWeightConstrainedPath_npComplete :
    shortestWeightConstrainedPathDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L shortestWeightConstrainedPathDec

end MetaMathlibExt.Complexity.NPComplete.ShortestWeightConstrainedPath
