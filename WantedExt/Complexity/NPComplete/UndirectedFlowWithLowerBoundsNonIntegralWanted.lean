/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNDIRECTED FLOW WITH LOWER BOUNDS with non-integral flows is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 216, problem [ND37] UNDIRECTED FLOW
WITH LOWER BOUNDS, comment: "Problem is NP-complete in the strong sense, even if
non-integral flows are allowed";
A. Itai, "Two-commodity flow", Journal of the ACM 25 (1978), 596-611,
doi:10.1145/322092.322100 (the reference Garey and Johnson give for [ND37]).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.UndirectedFlowWithLowerBoundsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UndirectedFlowWithLowerBoundsNonIntegral

open MetaMathlibExt.Complexity.NPComplete.UndirectedFlowWithLowerBounds
open MathlibExt.Combinatorics.Graph.MaxFlowMinCutWanted

/-!
# UNDIRECTED FLOW WITH LOWER BOUNDS with non-integral flows is NP-complete

INSTANCE: a graph `G = (V, E)`, specified vertices `s` and `t`, a capacity `c(e) ∈ ℤ⁺` and a
lower bound `l(e) ∈ ℤ₀⁺` for each `e ∈ E`, and a requirement `R ∈ ℤ⁺`. QUESTION: is there a
flow function `f : {(u, v), (v, u) : {u, v} ∈ E} → ℝ`, nonnegative but not necessarily integral,
such that for each `{u, v} ∈ E` either `f(u, v) = 0` or `f(v, u) = 0`,
`l({u, v}) ≤ max (f(u, v), f(v, u)) ≤ c({u, v})`, flow is conserved at every vertex other than
`s` and `t`, and the net flow into `t` is at least `R`?

This is UNDIRECTED FLOW WITH LOWER BOUNDS
(`WantedExt.Complexity.NPComplete.UndirectedFlowWithLowerBoundsWanted`) with the flow values
allowed to be arbitrary nonnegative reals instead of nonnegative integers. The instance, its
`WellFormed`, the graph `Graph`, the symmetric capacity `capacity` and the lower bound
`lowerBound` are reused unchanged; only the flow's codomain changes, from `ℕ` to `ℝ`
(nonnegativity is part of `IsFeasibleFlow`). The capacities, lower bounds and requirement are
still integers in binary.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- There is a real-valued flow `f` from `s` to `t` that is feasible for the symmetric edge
capacities (it is nonnegative, vanishes off the orientations of the edges, is at most
`c({u, v})` on both orientations of `{u, v}`, and is conserved at every vertex other than `s`
and `t`), uses only one direction of each edge, meets each lower bound in the used direction,
and has net flow into `t` at least `R`. -/
def NonIntegralFeasible (i : UndirectedFlowWithLowerBoundsInstance) : Prop :=
  ∃ (hs : i.2.2.1 < i.1) (ht : i.2.2.2.1 < i.1) (f : Fin i.1 → Fin i.1 → ℝ),
    IsFeasibleFlow (fun u v : Fin i.1 => (capacity i u v : ℝ)) ⟨i.2.2.1, hs⟩ ⟨i.2.2.2.1, ht⟩ f ∧
      (∀ u v, (Graph i).Adj u v →
        (f u v = 0 ∨ f v u = 0) ∧ (lowerBound i u v : ℝ) ≤ max (f u v) (f v u)) ∧
      (i.2.2.2.2 : ℝ) ≤ (∑ u, f u ⟨i.2.2.2.1, ht⟩) - ∑ w, f ⟨i.2.2.2.1, ht⟩ w

open Classical in
/-- UNDIRECTED FLOW WITH LOWER BOUNDS with non-integral flows, as a decision problem over
bitstrings. -/
noncomputable def nonIntegralDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UndirectedFlowWithLowerBoundsInstance) x with
  | some i => decide (WellFormed i ∧ NonIntegralFeasible i)
  | none => false

/-- **UNDIRECTED FLOW WITH LOWER BOUNDS remains NP-complete when non-integral flows are
allowed.** Source: Garey and Johnson (1979), [ND37], comment; Itai (1978). -/
public theorem_wanted undirectedFlowWithLowerBoundsNonIntegral_npComplete :
    nonIntegralDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nonIntegralDec

end MetaMathlibExt.Complexity.NPComplete.UndirectedFlowWithLowerBoundsNonIntegral
