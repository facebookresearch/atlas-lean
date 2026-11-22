/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNDIRECTED TWO-COMMODITY INTEGRAL FLOW is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND39] UNDIRECTED
TWO-COMMODITY INTEGRAL FLOW;
S. Even, A. Itai, and A. Shamir, "On the complexity of timetable and
multicommodity flow problems", SIAM Journal on Computing 5 (1976), 691-703,
doi:10.1137/0205048.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.Graph.MaxFlowMinCut
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UndirectedTwoCommodityIntegralFlow

/-!
# UNDIRECTED TWO-COMMODITY INTEGRAL FLOW is NP-complete

INSTANCE: a graph `G = (V, E)`, specified vertices `s₁`, `s₂`, `t₁`, `t₂`, a capacity
`c(e) ∈ ℤ⁺` for each `e ∈ E`, and requirements `R₁, R₂ ∈ ℤ⁺`. QUESTION: are there two flow
functions `f₁, f₂ : {(u, v), (v, u) : {u, v} ∈ E} → ℤ₀⁺` such that, for each `{u, v} ∈ E`,
`f₁(u, v) + f₁(v, u) + f₂(u, v) + f₂(v, u) ≤ c({u, v})`, each `fᵢ` is conserved at every vertex
other than `sᵢ` and `tᵢ`, and the net flow of `fᵢ` into `tᵢ` is at least `Rᵢ`, for `i = 1, 2`?

The vertices are `0, ..., n - 1`. Each edge is a record `(u, v, c)`: the edge `{u, v}` with
capacity `c`; there are no self-loops and at most one record per unordered pair. Commodity `i`
is the triple `(sᵢ, tᵢ, Rᵢ)`. A flow is a function `f : Fin n → Fin n → ℕ` (integral and
nonnegative) on ordered pairs. Each commodity's flow is checked with `IsFeasibleFlow` from
`MathlibExt.Combinatorics.Graph.MaxFlowMinCut` against the symmetric capacity `capacity`
(`c({u, v})` on both orientations of an edge, `0` elsewhere), so it vanishes off the two
orientations of the edges and is conserved at every vertex other than its own source and sink.
The joint capacity condition and the requirement on the net flow into `tᵢ` are stated directly.

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

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), edge records `(u, v, c)` (edge
`{u, v}` with capacity `c`), and the two commodities `(s₁, t₁, R₁)` and `(s₂, t₂, R₂)`. -/
abbrev UndirectedTwoCommodityIntegralFlowInstance :=
  ℕ × List (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)

/-- The endpoint pairs `(u, v)` of the edge records. -/
def endpoints (i : UndirectedTwoCommodityIntegralFlowInstance) : List (ℕ × ℕ) :=
  i.2.1.map fun e => (e.1, e.2.1)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : UndirectedTwoCommodityIntegralFlowInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (endpoints i)

/-- The capacity `c({u, v})` of the edge `{u, v}`, matched in either orientation, and `0` when
`{u, v}` is not an edge. -/
def capacity (i : UndirectedTwoCommodityIntegralFlowInstance) (u v : ℕ) : ℕ :=
  ((i.2.1.find? fun e => (e.1 = u ∧ e.2.1 = v) ∨ (e.1 = v ∧ e.2.1 = u)).map
    fun e => e.2.2).getD 0

/-- Well-formedness of an instance: the edge records describe a simple graph on
`0, ..., n - 1` (endpoints in range, no self-loops, at most one record per unordered pair),
every capacity is positive, and for each commodity `(sᵢ, tᵢ, Rᵢ)` the terminals are vertices and
the requirement is positive. -/
def WellFormed (i : UndirectedTwoCommodityIntegralFlowInstance) : Prop :=
  ((endpoints i).Nodup ∧ ∀ e ∈ endpoints i,
      e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ endpoints i) ∧
    (∀ e ∈ i.2.1, 0 < e.2.2) ∧
    (i.2.2.1.1 < i.1 ∧ i.2.2.1.2.1 < i.1 ∧ 0 < i.2.2.1.2.2) ∧
    (i.2.2.2.1 < i.1 ∧ i.2.2.2.2.1 < i.1 ∧ 0 < i.2.2.2.2.2)

/-- `f` is an integral flow for the commodity `(s, t, R)`: it is feasible for the symmetric edge
capacities (it vanishes off the orientations of the edges, is at most `c({u, v})` on both
orientations of `{u, v}`, and is conserved at every vertex other than `s` and `t`), and its net
flow into `t` is at least `R`. -/
def CommodityFlow (i : UndirectedTwoCommodityIntegralFlowInstance) (st : ℕ × ℕ × ℕ)
    (f : Fin i.1 → Fin i.1 → ℕ) : Prop :=
  ∃ (hs : st.1 < i.1) (ht : st.2.1 < i.1),
    IsFeasibleFlow (fun u v : Fin i.1 => (capacity i u v : ℝ)) ⟨st.1, hs⟩ ⟨st.2.1, ht⟩
        (fun u v => (f u v : ℝ)) ∧
      (st.2.2 : ℝ) ≤ (∑ u, (f u ⟨st.2.1, ht⟩ : ℝ)) - ∑ w, (f ⟨st.2.1, ht⟩ w : ℝ)

/-- There are integral flows `f₁` for commodity 1 and `f₂` for commodity 2 such that, on each
edge `{u, v}`, the flows of both commodities in both directions add up to at most
`c({u, v})`. -/
def UndirectedTwoCommodityIntegralFlowFeasible
    (i : UndirectedTwoCommodityIntegralFlowInstance) : Prop :=
  ∃ f₁ f₂ : Fin i.1 → Fin i.1 → ℕ,
    (∀ u v, (Graph i).Adj u v →
      f₁ u v + f₁ v u + f₂ u v + f₂ v u ≤ capacity i u v) ∧
      CommodityFlow i i.2.2.1 f₁ ∧ CommodityFlow i i.2.2.2 f₂

open Classical in
/-- UNDIRECTED TWO-COMMODITY INTEGRAL FLOW as a decision problem over bitstrings. -/
noncomputable def undirectedTwoCommodityIntegralFlowDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UndirectedTwoCommodityIntegralFlowInstance) x with
  | some i => decide (WellFormed i ∧ UndirectedTwoCommodityIntegralFlowFeasible i)
  | none => false

/-- **UNDIRECTED TWO-COMMODITY INTEGRAL FLOW is NP-complete.** Source: Garey and Johnson (1979),
[ND39]; Even, Itai, and Shamir (1976). -/
public theorem_wanted undirectedTwoCommodityIntegralFlow_npComplete :
    undirectedTwoCommodityIntegralFlowDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L undirectedTwoCommodityIntegralFlowDec

end MetaMathlibExt.Complexity.NPComplete.UndirectedTwoCommodityIntegralFlow
