/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RATIO-CUT is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, MINIMUM RATIO-CUT;
D. W. Matula and F. Shahrokhi, "Sparsest cuts and bottlenecks in graphs", Discrete Applied
Mathematics 27 (1990), 113-123, doi:10.1016/0166-218X(90)90133-W;
A. Gupta, K. Talwar and D. Witmer, "Sparsest cut on bounded treewidth graphs: algorithms and
hardness results", STOC 2013, 281-290, doi:10.1145/2488608.2488644 (Section 1, recording the
result).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RatioCut

/-!
# RATIO-CUT is NP-complete

INSTANCE: a graph `G = (V, E)`, a capacity function `c : E → ℕ`, `k` commodities, i.e. `k`
pairs `(s_i, t_i) ∈ V²` with a demand `d_i` for each pair, and a positive integer `K`.
QUESTION: is there a cut, i.e. a partition of `V` into two disjoint sets `V₁` and `V₂`, whose
capacity divided by the demand across it,
`∑_{v₁ ∈ V₁, v₂ ∈ V₂, (v₁, v₂) ∈ E} c(v₁, v₂) / ∑_{i : |{s_i, t_i} ∩ V₁| = 1} d_i`,
is at most `K`?

This is the decision version of Crescenzi and Kann's MINIMUM RATIO-CUT, whose instance
is the general (non-uniform) one: "Graph `G = (V, E)`, a capacity function `c : E → N`, and `k`
commodities, i.e., `k` pairs `(s_i, t_i) ∈ V²` and a demand `d_i` for each pair", with measure
"the capacity of the cut divided by the demand across the cut"; their comment calls it Sparsest
Cut and treats "the uniform-demand case" separately. `UniformSparsestCut` is that special case
(unit capacities, one unit-demand commodity for every pair of vertices); Matula and Shahrokhi
prove that case NP-hard (Gupta, Talwar and Witmer, Section 1: NP-hard "even for unit capacity
edges and uniform demands"). An integer bound loses nothing: scaling the capacities by `q` and
the demands by `p` turns a rational bound `p / q` into `1`. Membership in NP: `V₁` is a
certificate.

The ratio is defined only when the demand across the cut is positive, so a cut qualifies when
that demand is positive and the capacity is at most `K` times it (no division); a positive
demand across the cut also makes both sides nonempty. The vertices are `0, ..., n - 1`, `V₁` is
a finite set of vertices and `V₂ = V − V₁`, so an edge joins `V₁` to `V₂` iff exactly one of its
endpoints is in `V₁`. The edges `(u, v, c(e))` form a simple graph (no self-loops, at most one
edge per unordered pair), so every edge is counted once. The commodities `(s_i, t_i, d_i)` have
`s_i ≠ t_i`, so `|{s_i, t_i} ∩ V₁| = 1` says that exactly one of `s_i`, `t_i` is in `V₁`.
Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the vertex count `n`, the edges `(u, v, c(e))`, the commodities
`(s_i, t_i, d_i)`, and the bound `K`. -/
abbrev RatioCutInstance := ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: every edge joins two different vertices below `n`, with at
most one edge per unordered pair; every commodity joins two different vertices below `n`; and
`0 < K`. -/
def WellFormed (i : RatioCutInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1) ∧
    (∀ e1 ∈ i.2.1, ∀ e2 ∈ i.2.1,
      (e1.1 = e2.1 ∧ e1.2.1 = e2.2.1 ∨ e1.1 = e2.2.1 ∧ e1.2.1 = e2.1) → e1 = e2) ∧
    (∀ q ∈ i.2.2.1, q.1 < i.1 ∧ q.2.1 < i.1 ∧ q.1 ≠ q.2.1) ∧ 0 < i.2.2.2

/-- The capacity of the cut `(V₁, V − V₁)`: the total capacity of the edges with exactly one
endpoint in `V₁`. -/
def capacity (i : RatioCutInstance) (V₁ : Finset ℕ) : ℕ :=
  ((i.2.1.filter fun e => decide (e.1 ∈ V₁) ≠ decide (e.2.1 ∈ V₁)).map fun e => e.2.2).sum

/-- The demand across the cut `(V₁, V − V₁)`: the total demand of the commodities with exactly
one of `s_i`, `t_i` in `V₁`. -/
def demand (i : RatioCutInstance) (V₁ : Finset ℕ) : ℕ :=
  ((i.2.2.1.filter fun q => decide (q.1 ∈ V₁) ≠ decide (q.2.1 ∈ V₁)).map fun q => q.2.2).sum

/-- Some cut `(V₁, V − V₁)` has positive demand across it and ratio at most `K`. -/
def RatioCutFeasible (i : RatioCutInstance) : Prop :=
  ∃ V₁ : Finset ℕ, (∀ v ∈ V₁, v < i.1) ∧ 0 < demand i V₁ ∧
    capacity i V₁ ≤ i.2.2.2 * demand i V₁

open Classical in
/-- RATIO-CUT as a decision problem over bitstrings. -/
noncomputable def ratioCutDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RatioCutInstance) x with
  | some i => decide (WellFormed i ∧ RatioCutFeasible i)
  | none => false

/-- **RATIO-CUT is NP-complete.** Source: Crescenzi and Kann, MINIMUM RATIO-CUT; Matula and
Shahrokhi (1990); Gupta, Talwar and Witmer (2013). -/
public theorem_wanted ratioCut_npComplete :
    ratioCutDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L ratioCutDec

end MetaMathlibExt.Complexity.NPComplete.RatioCut
