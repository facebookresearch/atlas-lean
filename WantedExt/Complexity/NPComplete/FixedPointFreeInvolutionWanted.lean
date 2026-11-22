/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FIXED-POINT-FREE AUTOMORPHISM OF ORDER 2 is NP-complete

Source:
A. Lubiw, "Some NP-complete problems similar to graph isomorphism", SIAM Journal on Computing
10 (1981), 11-21, doi:10.1137/0210002 (original not available here; the abstract: "the problem of
determining whether a given graph has a fixed-point-free automorphism" is NP-complete);
A. Abiad, G. Coutinho, E. Juliano, V. F. dos Santos and S. Zeijlemaker, "Computing fixed point
free automorphisms of graphs", arXiv:2603.26006 (2026), Section 1 ("FPF involutions, that is,
FPF automorphisms of order two. The problem of finding involutions without fixed points
(FPFInv) is also NP-hard [Lubiw]").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Algebra.Order.Group.End
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.GroupTheory.OrderOfElement
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FixedPointFreeInvolution

/-!
# FIXED-POINT-FREE AUTOMORPHISM OF ORDER 2 is NP-complete

INSTANCE: a graph `G = (V, E)`. QUESTION: does `G` have an automorphism `f` of order `2` with
`f(v) ≠ v` for every `v ∈ V` (a fixed-point-free involution)?

Abiad et al. (Section 1) state the fixed point free automorphism problem ("given a graph `G`,
determine whether there exists an automorphism `ϕ : V(G) → V(G)` such that `ϕ(u) ≠ u` for every
`u ∈ V(G)`", NP-complete by Lubiw) and record that its restriction to "FPF involutions, that is,
FPF automorphisms of order two" is "also NP-hard [Lubiw]".

An automorphism is a Mathlib graph isomorphism `f : Graph i ≃g Graph i`; these form a group
(Mathlib's `Group (r ≃r r)`, composition), and "order 2" is Mathlib's `orderOf f = 2`. Together
with "no fixed vertex" this excludes the graph with no vertices, whose only automorphism is the
identity (order `1`). The graph is given by an edge list on `Fin n`
(`Cslib.Complexity.Karp.edgeGraph`). The vertex count is binary, so a whole permutation of
`Fin n` is not a polynomial certificate; but an automorphism maps isolated vertices to isolated
vertices, and the isolated vertices have a fixed-point-free involution exactly when their number
is even, so the involution on the non-isolated vertices (all named in the edge list) together
with that parity check is one, and membership in NP holds for this encoding. This module is
independent of the FIXED-POINT-FREE AUTOMORPHISM statement (same instance encoding).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev FixedPointFreeInvolutionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : FixedPointFreeInvolutionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : FixedPointFreeInvolutionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- The graph has an automorphism of order `2` that fixes no vertex. -/
def FixedPointFreeInvolutionFeasible (i : FixedPointFreeInvolutionInstance) : Prop :=
  ∃ f : Graph i ≃g Graph i, orderOf f = 2 ∧ ∀ v, f v ≠ v

open Classical in
/-- FIXED-POINT-FREE AUTOMORPHISM OF ORDER 2 as a decision problem over bitstrings. -/
noncomputable def fixedPointFreeInvolutionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FixedPointFreeInvolutionInstance) x with
  | some i => decide (WellFormed i ∧ FixedPointFreeInvolutionFeasible i)
  | none => false

/-- **FIXED-POINT-FREE AUTOMORPHISM OF ORDER 2 is NP-complete.** Source: Lubiw (1981). -/
public theorem_wanted fixedPointFreeInvolution_npComplete :
    fixedPointFreeInvolutionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L fixedPointFreeInvolutionDec

end MetaMathlibExt.Complexity.NPComplete.FixedPointFreeInvolution
