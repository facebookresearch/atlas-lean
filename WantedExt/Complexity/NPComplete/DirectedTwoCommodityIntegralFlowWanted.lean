/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED TWO-COMMODITY INTEGRAL FLOW is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND38] DIRECTED
TWO-COMMODITY INTEGRAL FLOW;
S. Even, A. Itai, and A. Shamir, "On the complexity of timetable and
multicommodity flow problems", SIAM Journal on Computing 5 (1976), 691-703,
doi:10.1137/0205048.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Combinatorics.Graph.MaxFlowMinCut
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedTwoCommodityIntegralFlow

/-!
# DIRECTED TWO-COMMODITY INTEGRAL FLOW is NP-complete

INSTANCE: a directed graph `G = (V, A)`, specified vertices `s₁`, `s₂`, `t₁`, `t₂`, a capacity
`c(a) ∈ ℤ⁺` for each `a ∈ A`, and requirements `R₁, R₂ ∈ ℤ⁺`. QUESTION: are there two flow
functions `f₁, f₂ : A → ℤ₀⁺` such that `f₁(a) + f₂(a) ≤ c(a)` for each `a ∈ A`, each `fᵢ` is
conserved at every vertex other than `sᵢ` and `tᵢ`, and the net flow of `fᵢ` into `tᵢ` is at
least `Rᵢ`, for `i = 1, 2`?

The vertices are `0, ..., n - 1`. Each arc is a record `(u, v, c)`: the arc from `u` to `v` with
capacity `c`; there are no self-loops and no repeated arcs. Commodity `i` is the triple
`(sᵢ, tᵢ, Rᵢ)`. A flow is a function `f : Fin n → Fin n → ℕ` (integral and nonnegative) on
ordered pairs. Each commodity's flow is checked with `IsFeasibleFlow` from
`MathlibExt.Combinatorics.Graph.MaxFlowMinCut` against the arc capacities `capacity` (`c(a)` on
an arc `a`, `0` on every other ordered pair), so it vanishes off the arcs (it is a function on
`A`) and is conserved at every vertex other than its own source and sink. The joint capacity
constraint and the requirement on the net flow into `tᵢ` are stated directly.

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

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), arc records `(u, v, c)` (arc from
`u` to `v` with capacity `c`), and the two commodities `(s₁, t₁, R₁)` and `(s₂, t₂, R₂)`. -/
abbrev DirectedTwoCommodityIntegralFlowInstance :=
  ℕ × List (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)

/-- The arcs `(u, v)` of the arc records. -/
def arcs (i : DirectedTwoCommodityIntegralFlowInstance) : List (ℕ × ℕ) :=
  i.2.1.map fun a => (a.1, a.2.1)

/-- The capacity `c(u, v)` of the arc from `u` to `v`, and `0` when there is no such arc. -/
def capacity (i : DirectedTwoCommodityIntegralFlowInstance) (u v : ℕ) : ℕ :=
  ((i.2.1.find? fun a => a.1 = u ∧ a.2.1 = v).map fun a => a.2.2).getD 0

/-- Well-formedness of an instance: the arc records describe a directed graph on
`0, ..., n - 1` (endpoints in range, no self-loops, no repeated arcs), every capacity is
positive, and for each commodity `(sᵢ, tᵢ, Rᵢ)` the terminals are vertices and the requirement
is positive. -/
def WellFormed (i : DirectedTwoCommodityIntegralFlowInstance) : Prop :=
  ((arcs i).Nodup ∧ ∀ a ∈ arcs i, a.1 < i.1 ∧ a.2 < i.1 ∧ a.1 ≠ a.2) ∧
    (∀ a ∈ i.2.1, 0 < a.2.2) ∧
    (i.2.2.1.1 < i.1 ∧ i.2.2.1.2.1 < i.1 ∧ 0 < i.2.2.1.2.2) ∧
    (i.2.2.2.1 < i.1 ∧ i.2.2.2.2.1 < i.1 ∧ 0 < i.2.2.2.2.2)

/-- `f` is an integral flow for the commodity `(s, t, R)`: it is feasible for the arc capacities
(it vanishes off the arcs, is at most the capacity on each arc, and is conserved at every vertex
other than `s` and `t`), and its net flow into `t` is at least `R`. -/
def CommodityFlow (i : DirectedTwoCommodityIntegralFlowInstance) (st : ℕ × ℕ × ℕ)
    (f : Fin i.1 → Fin i.1 → ℕ) : Prop :=
  ∃ (hs : st.1 < i.1) (ht : st.2.1 < i.1),
    IsFeasibleFlow (fun u v : Fin i.1 => (capacity i u v : ℝ)) ⟨st.1, hs⟩ ⟨st.2.1, ht⟩
        (fun u v => (f u v : ℝ)) ∧
      (st.2.2 : ℝ) ≤ (∑ u, (f u ⟨st.2.1, ht⟩ : ℝ)) - ∑ w, (f ⟨st.2.1, ht⟩ w : ℝ)

/-- There are integral flows `f₁` for commodity 1 and `f₂` for commodity 2 whose sum on each arc
is at most its capacity. -/
def DirectedTwoCommodityIntegralFlowFeasible
    (i : DirectedTwoCommodityIntegralFlowInstance) : Prop :=
  ∃ f₁ f₂ : Fin i.1 → Fin i.1 → ℕ,
    (∀ u v, f₁ u v + f₂ u v ≤ capacity i u v) ∧
      CommodityFlow i i.2.2.1 f₁ ∧ CommodityFlow i i.2.2.2 f₂

open Classical in
/-- DIRECTED TWO-COMMODITY INTEGRAL FLOW as a decision problem over bitstrings. -/
noncomputable def directedTwoCommodityIntegralFlowDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DirectedTwoCommodityIntegralFlowInstance) x with
  | some i => decide (WellFormed i ∧ DirectedTwoCommodityIntegralFlowFeasible i)
  | none => false

/-- **DIRECTED TWO-COMMODITY INTEGRAL FLOW is NP-complete.** Source: Garey and Johnson (1979),
[ND38]; Even, Itai, and Shamir (1976). -/
public theorem_wanted directedTwoCommodityIntegralFlow_npComplete :
    directedTwoCommodityIntegralFlowDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L directedTwoCommodityIntegralFlowDec

end MetaMathlibExt.Complexity.NPComplete.DirectedTwoCommodityIntegralFlow
