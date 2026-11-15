/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM k-CUT is NP-complete

Source:
O. Goldschmidt and D. S. Hochbaum, "A polynomial algorithm for the k-cut problem for fixed k",
Mathematics of Operations Research 19 (1994), 24-37, doi:10.1287/moor.19.1.24.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumKCut

/-!
# MINIMUM k-CUT is NP-complete

INSTANCE: a graph `G = (V, E)` with edge weights `w : E → ℕ`, an integer `k` with
`2 ≤ k ≤ |V|` (part of the input), and a bound `B`. QUESTION: is there a partition of `V` into
`k` nonempty sets such that the total weight of the edges joining different sets is at most
`B`?

Goldschmidt and Hochbaum (abstract): "The k-cut problem is to find a partition of an edge
weighted graph into k nonempty components, such that the total edge weight between components
is minimum. This problem is NP-complete for an arbitrary k". The decision form bounds that
weight by `B`. Equivalently, some edge set of weight at most `B` leaves at least `k` connected
components when removed (weights are nonnegative). The range `2 ≤ k ≤ |V|` is that of the
problem's entry MINIMUM K-CUT in the Crescenzi-Kann compendium of NP optimization
problems.

The graph is simple, given by a list of weighted edges `(u, v, w)` on the vertices
`0, …, n - 1`. A partition into `k` nonempty sets is a map `part` from the vertices onto
`0, …, k - 1`. Weights use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number of vertices `n`, the weighted edges `(u, v, w)`, the number of
parts `k`, and the bound `B`. -/
abbrev MinimumKCutInstance := ℕ × List (ℕ × ℕ × ℕ) × ℕ × ℕ

/-- Well-formedness of an instance: the edges form a simple graph on `0, …, n - 1` (no loops,
no edge listed twice in either orientation), and `2 ≤ k ≤ n`. -/
def WellFormed (i : MinimumKCutInstance) : Prop :=
  (i.2.1.map fun e => (e.1, e.2.1)).Nodup ∧
    (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧
      ∀ e' ∈ i.2.1, (e'.1, e'.2.1) ≠ (e.2.1, e.1)) ∧
    2 ≤ i.2.2.1 ∧ i.2.2.1 ≤ i.1

/-- The total weight of the edges whose endpoints lie in different parts of `part`. -/
def cutWeight (edges : List (ℕ × ℕ × ℕ)) (part : ℕ → ℕ) : ℕ :=
  ((edges.filter fun e => part e.1 ≠ part e.2.1).map fun e => e.2.2).sum

/-- Some map `part` from the vertices onto `0, …, k - 1` (a partition into `k` nonempty sets)
has cut weight at most `B`. -/
def MinimumKCutFeasible (i : MinimumKCutInstance) : Prop :=
  ∃ part : ℕ → ℕ, (∀ v < i.1, part v < i.2.2.1) ∧ (∀ c < i.2.2.1, ∃ v < i.1, part v = c) ∧
    cutWeight i.2.1 part ≤ i.2.2.2

open Classical in
/-- MINIMUM k-CUT as a decision problem over bitstrings. -/
noncomputable def minimumKCutDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumKCutInstance) x with
  | some i => decide (WellFormed i ∧ MinimumKCutFeasible i)
  | none => false

/-- **MINIMUM k-CUT is NP-complete** (with `k` part of the input). Source: Goldschmidt and
Hochbaum (1994). -/
public theorem_wanted minimumKCut_npComplete :
    minimumKCutDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumKCutDec

end MetaMathlibExt.Complexity.NPComplete.MinimumKCut
