/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNIFORM SPARSEST CUT is NP-complete

Source:
D. W. Matula and F. Shahrokhi, "Sparsest cuts and bottlenecks in graphs", Discrete Applied
Mathematics 27 (1990), 113-123, doi:10.1016/0166-218X(90)90133-W;
A. Gupta, K. Talwar and D. Witmer, "Sparsest cut on bounded treewidth graphs: algorithms and
hardness results", STOC 2013, doi:10.1145/2488608.2488644 (Section 1, recording the result).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import Mathlib.Data.Finset.Card
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UniformSparsestCut

/-!
# UNIFORM SPARSEST CUT is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive rational `r`. QUESTION: is there a set `S ⊆ V`
with `0 < |S| < |V|` whose sparsity `|E(S, V - S)| / (|S| · |V - S|)` is at most `r`, where
`E(S, V - S)` is the set of edges with exactly one end in `S`?

This is the Sparsest Cut problem with unit edge capacities and uniform demands (one unit of
demand between every pair of vertices), whose denominator `|S| · |V - S|` counts the pairs of
vertices separated by the cut. Matula and Shahrokhi prove it NP-hard (Gupta, Talwar and Witmer,
Section 1: NP-hard "even for unit capacity edges and uniform demands"). Membership in NP: `S`
is a certificate.

The vertices are `0, ..., n - 1` and the edges a simple edge list, so its length is `|E|`. The
bound is `r = num / den`, and the sparsity condition is written without division as
`|E(S, V - S)| · den ≤ num · |S| · (n - |S|)`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of vertices, the edge list, and the bound `r` as a pair
`(num, den)` standing for `num / den`. -/
abbrev UniformSparsestCutInstance := ℕ × List (ℕ × ℕ) × (ℕ × ℕ)

/-- Well-formedness of an instance: the edge list describes a simple graph on `0, ..., n - 1`,
and `r = num / den` has a positive denominator and is positive. -/
def WellFormed (i : UniformSparsestCutInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2.2 ∧ 0 < i.2.2.1

/-- The number of edges with exactly one end in `S`. -/
def cutSize (i : UniformSparsestCutInstance) (S : Finset ℕ) : ℕ :=
  (i.2.1.filter fun e => decide ((e.1 ∈ S ∧ e.2 ∉ S) ∨ (e.1 ∉ S ∧ e.2 ∈ S))).length

/-- Some vertex set `S` with `0 < |S| < n` has sparsity
`cutSize S / (|S| · (n - |S|)) ≤ num / den`. -/
def UniformSparsestCutFeasible (i : UniformSparsestCutInstance) : Prop :=
  ∃ S : Finset ℕ, (∀ v ∈ S, v < i.1) ∧ 0 < S.card ∧ S.card < i.1 ∧
    cutSize i S * i.2.2.2 ≤ i.2.2.1 * (S.card * (i.1 - S.card))

open Classical in
/-- UNIFORM SPARSEST CUT as a decision problem over bitstrings. -/
noncomputable def uniformSparsestCutDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UniformSparsestCutInstance) x with
  | some i => decide (WellFormed i ∧ UniformSparsestCutFeasible i)
  | none => false

/-- **UNIFORM SPARSEST CUT is NP-complete.** Source: Matula and Shahrokhi (1990); Gupta,
Talwar and Witmer (2013). -/
public theorem_wanted uniformSparsestCut_npComplete :
    uniformSparsestCutDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L uniformSparsestCutDec

end MetaMathlibExt.Complexity.NPComplete.UniformSparsestCut
