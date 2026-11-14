/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNDIRECTED FLOW WITH LOWER BOUNDS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND37] UNDIRECTED FLOW
WITH LOWER BOUNDS;
A. Itai, "Two-commodity flow", Journal of the ACM 25 (1978), 596-611,
doi:10.1145/322092.322100.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.Graph.MaxFlowMinCut
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UndirectedFlowWithLowerBounds

/-!
# UNDIRECTED FLOW WITH LOWER BOUNDS is NP-complete

INSTANCE: a graph `G = (V, E)`, specified vertices `s` and `t`, a capacity `c(e) ∈ ℤ⁺` and a
lower bound `l(e) ∈ ℤ₀⁺` with `l(e) ≤ c(e)` for each `e ∈ E`, and a requirement `R ∈ ℤ⁺`.
QUESTION: is there a flow function `f : {(u, v), (v, u) : {u, v} ∈ E} → ℤ₀⁺` such that for each
`{u, v} ∈ E` either `f(u, v) = 0` or `f(v, u) = 0`,
`l({u, v}) ≤ max (f(u, v), f(v, u)) ≤ c({u, v})`, flow is conserved at every vertex other than
`s` and `t`, and the net flow into `t` is at least `R`?

The vertices are `0, ..., n - 1`. Each edge is a record `(u, v, l, c)`: the edge `{u, v}` with
lower bound `l` and capacity `c`; there are no self-loops and at most one record per unordered
pair. A flow is a function `f : Fin n → Fin n → ℕ` (integral and nonnegative) on ordered
pairs; it is checked with `IsFeasibleFlow` from `MathlibExt.Combinatorics.Graph.MaxFlowMinCut`
against the symmetric capacity `capacity`, which is `c({u, v})` on both orientations of an edge
and `0` elsewhere. So `f` vanishes off the two orientations of the edges, `f(u, v) ≤ c({u, v})`
and `f(v, u) ≤ c({u, v})` (that is, `max (f(u, v), f(v, u)) ≤ c({u, v})`), and flow is
conserved at every vertex other than `s` and `t`. The remaining edge conditions (one direction
carries no flow, and the larger direction meets the lower bound) and the requirement on the net
flow into `t` are stated directly.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), edge records `(u, v, l, c)` (edge
`{u, v}` with lower bound `l` and capacity `c`), source `s`, sink `t`, requirement `R`. -/
abbrev UndirectedFlowWithLowerBoundsInstance := ℕ × List (ℕ × ℕ × ℕ × ℕ) × ℕ × ℕ × ℕ

/-- The endpoint pairs `(u, v)` of the edge records. -/
def endpoints (i : UndirectedFlowWithLowerBoundsInstance) : List (ℕ × ℕ) :=
  i.2.1.map fun e => (e.1, e.2.1)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : UndirectedFlowWithLowerBoundsInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (endpoints i)

/-- The record of the edge `{u, v}`, matched in either orientation, if there is one. -/
def edgeRecord (i : UndirectedFlowWithLowerBoundsInstance) (u v : ℕ) :
    Option (ℕ × ℕ × ℕ × ℕ) :=
  i.2.1.find? fun e => (e.1 = u ∧ e.2.1 = v) ∨ (e.1 = v ∧ e.2.1 = u)

/-- The capacity `c({u, v})` of the edge `{u, v}`, and `0` when `{u, v}` is not an edge. -/
def capacity (i : UndirectedFlowWithLowerBoundsInstance) (u v : ℕ) : ℕ :=
  ((edgeRecord i u v).map fun e => e.2.2.2).getD 0

/-- The lower bound `l({u, v})` of the edge `{u, v}`, and `0` when `{u, v}` is not an edge. -/
def lowerBound (i : UndirectedFlowWithLowerBoundsInstance) (u v : ℕ) : ℕ :=
  ((edgeRecord i u v).map fun e => e.2.2.1).getD 0

/-- Well-formedness of an instance: the edge records describe a simple graph on
`0, ..., n - 1` (endpoints in range, no self-loops, at most one record per unordered pair),
every capacity is positive and at least the edge's lower bound, `s` and `t` are vertices, and
the requirement `R` is positive. -/
def WellFormed (i : UndirectedFlowWithLowerBoundsInstance) : Prop :=
  ((endpoints i).Nodup ∧ ∀ e ∈ endpoints i,
      e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ endpoints i) ∧
    (∀ e ∈ i.2.1, 0 < e.2.2.2 ∧ e.2.2.1 ≤ e.2.2.2) ∧
    i.2.2.1 < i.1 ∧ i.2.2.2.1 < i.1 ∧ 0 < i.2.2.2.2

/-- There is an integral flow `f` from `s` to `t` that is feasible for the symmetric edge
capacities (it vanishes off the orientations of the edges, is at most `c({u, v})` on both
orientations of `{u, v}`, and is conserved at every vertex other than `s` and `t`), uses only
one direction of each edge, meets each lower bound in the used direction, and has net flow into
`t` at least `R`. -/
def UndirectedFlowWithLowerBoundsFeasible
    (i : UndirectedFlowWithLowerBoundsInstance) : Prop :=
  ∃ (hs : i.2.2.1 < i.1) (ht : i.2.2.2.1 < i.1) (f : Fin i.1 → Fin i.1 → ℕ),
    IsFeasibleFlow (fun u v : Fin i.1 => (capacity i u v : ℝ)) ⟨i.2.2.1, hs⟩ ⟨i.2.2.2.1, ht⟩
        (fun u v => (f u v : ℝ)) ∧
      (∀ u v, (Graph i).Adj u v →
        (f u v = 0 ∨ f v u = 0) ∧ lowerBound i u v ≤ max (f u v) (f v u)) ∧
      (i.2.2.2.2 : ℝ) ≤
        (∑ u, (f u ⟨i.2.2.2.1, ht⟩ : ℝ)) - ∑ w, (f ⟨i.2.2.2.1, ht⟩ w : ℝ)

open Classical in
/-- UNDIRECTED FLOW WITH LOWER BOUNDS as a decision problem over bitstrings. -/
noncomputable def undirectedFlowWithLowerBoundsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UndirectedFlowWithLowerBoundsInstance) x with
  | some i => decide (WellFormed i ∧ UndirectedFlowWithLowerBoundsFeasible i)
  | none => false

/-- **UNDIRECTED FLOW WITH LOWER BOUNDS is NP-complete.** Source: Garey and Johnson (1979),
[ND37]; Itai (1978). -/
public theorem_wanted undirectedFlowWithLowerBounds_npComplete :
    undirectedFlowWithLowerBoundsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L undirectedFlowWithLowerBoundsDec

end MetaMathlibExt.Complexity.NPComplete.UndirectedFlowWithLowerBounds
