/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FAULT DETECTION WITH TEST POINTS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MS19] FAULT DETECTION WITH TEST POINTS
(p. 284), credited there to [Ibaraki, Kameda, and Toida, 1977], "NP-complete diagnosis problems
on systems graphs", listed in the book's bibliography as an unpublished manuscript
(transformation from X3C).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FaultDetectionWithTestPoints

/-!
# FAULT DETECTION WITH TEST POINTS is NP-complete

INSTANCE: a directed acyclic graph `G = (V, A)` having exactly one vertex `s ∈ V` with in-degree
`0` and exactly one vertex `t ∈ V` with out-degree `0`, and a positive integer `K`. QUESTION:
can all "single faults" in `G` be located by attaching `K` or fewer "test points" to arcs in
`A`, i.e., is there a subset `A' ⊆ A` with `|A'| ≤ K` such that the test set
`T = ({s} ∪ {u₁ : (u₁, u₂) ∈ A'}) × ({t} ∪ {u₂ : (u₁, u₂) ∈ A'})` has the property that, for each
pair `v, v' ∈ V - {s, t}`, there is some `(u₁, u₂) ∈ T` such that `v` is on a directed path from
`u₁` to `u₂` but `v'` is on no such path?

The directed graph is Mathlib's `Digraph`. The vertices `s` and `t` are determined by `G`; the
instance lists them, and `WellFormed` checks that they are the unique vertex of in-degree `0` and
the unique vertex of out-degree `0`. A vertex `v` lies on a directed path from `u₁` to `u₂`
exactly when `u₁` reaches `v` and `v` reaches `u₂` (reachability is the reflexive-transitive
closure of the arc relation, so a path may have length zero; in an acyclic graph every walk is
a path). The condition is required for every ordered pair of distinct vertices `v ≠ v'` of
`V - {s, t}`, with the roles of `v` and `v'` as in the source.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), the arc list (a pair `(u, v)` is the arc
`u → v`), the source `s`, the sink `t`, and the bound `K`. -/
abbrev FaultDetectionWithTestPointsInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ × ℕ

/-- The directed graph of the instance, with an arc `u → v` for each pair `(u, v)` of the arc
list. -/
def Graph (i : FaultDetectionWithTestPointsInstance) : Digraph (Fin i.1) where
  Adj u v := ((u : ℕ), (v : ℕ)) ∈ i.2.1

/-- `v` lies on a directed path from `u₁` to `u₂`: `u₁` reaches `v` and `v` reaches `u₂`. -/
def OnPath (i : FaultDetectionWithTestPointsInstance) (u₁ v u₂ : Fin i.1) : Prop :=
  Relation.ReflTransGen (Graph i).Adj u₁ v ∧ Relation.ReflTransGen (Graph i).Adj v u₂

/-- Well-formedness of an instance: no repeated arcs, endpoints in range, no directed cycle
(this also excludes loops), `s` is the unique vertex of in-degree `0`, `t` is the unique vertex
of out-degree `0`, and `0 < K`. -/
def WellFormed (i : FaultDetectionWithTestPointsInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1) ∧
    (∀ v, ¬ Relation.TransGen (Graph i).Adj v v) ∧
    (∃ s : Fin i.1, (s : ℕ) = i.2.2.1 ∧ ∀ v, (∀ u, ¬ (Graph i).Adj u v) ↔ v = s) ∧
    (∃ t : Fin i.1, (t : ℕ) = i.2.2.2.1 ∧ ∀ v, (∀ w, ¬ (Graph i).Adj v w) ↔ v = t) ∧
    0 < i.2.2.2.2

/-- Some set `A'` of at most `K` arcs makes the test set
`T = ({s} ∪ {tails of A'}) × ({t} ∪ {heads of A'})` locate every single fault: for all distinct
`v, v' ∉ {s, t}` some `(u₁, u₂) ∈ T` has `v` on a directed path from `u₁` to `u₂` and `v'` on
no such path. -/
def FaultDetectionWithTestPointsFeasible (i : FaultDetectionWithTestPointsInstance) : Prop :=
  ∃ A' : Finset (Fin i.1 × Fin i.1), (∀ a ∈ A', (Graph i).Adj a.1 a.2) ∧ A'.card ≤ i.2.2.2.2 ∧
    ∀ v v' : Fin i.1, (v : ℕ) ≠ i.2.2.1 → (v : ℕ) ≠ i.2.2.2.1 → (v' : ℕ) ≠ i.2.2.1 →
      (v' : ℕ) ≠ i.2.2.2.1 → v ≠ v' →
        ∃ u₁ u₂ : Fin i.1, ((u₁ : ℕ) = i.2.2.1 ∨ ∃ w, (u₁, w) ∈ A') ∧
          ((u₂ : ℕ) = i.2.2.2.1 ∨ ∃ w, (w, u₂) ∈ A') ∧
          OnPath i u₁ v u₂ ∧ ¬ OnPath i u₁ v' u₂

open Classical in
/-- FAULT DETECTION WITH TEST POINTS as a decision problem over bitstrings. -/
noncomputable def faultDetectionWithTestPointsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FaultDetectionWithTestPointsInstance) x with
  | some i => decide (WellFormed i ∧ FaultDetectionWithTestPointsFeasible i)
  | none => false

/-- **FAULT DETECTION WITH TEST POINTS is NP-complete.** Source: Garey and Johnson (1979),
[MS19] (Ibaraki, Kameda, and Toida, unpublished). -/
public theorem_wanted faultDetectionWithTestPoints_npComplete :
    faultDetectionWithTestPointsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L faultDetectionWithTestPointsDec

end MetaMathlibExt.Complexity.NPComplete.FaultDetectionWithTestPoints
