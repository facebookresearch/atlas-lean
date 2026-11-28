/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

/-!
# FIXED-POINT-FREE AUTOMORPHISM: definitions

INSTANCE: a graph `G = (V, E)`. QUESTION: does `G` have an automorphism `f` with `f(v) ≠ v` for
every `v ∈ V`?

Abiad et al. (abstract): "In 1981, Lubiw proved that the fixed point free automorphism problem
(FPFAut) is NP-complete: given a graph `G`, determine whether there exists an automorphism
`ϕ : V(G) → V(G)` such that `ϕ(u) ≠ u` for every `u ∈ V(G)`", where "a bijection
`ϕ : V(G) → V(G)` is called an automorphism if `uv ∈ E(G) ⟺ ϕ(u)ϕ(v) ∈ E(G)`".

An automorphism is a Mathlib graph isomorphism `Graph i ≃g Graph i` (a bijection of the vertices
that preserves adjacency in both directions). The graph is given by an edge list on `Fin n`
(`Cslib.Complexity.Karp.edgeGraph`). The graph with no vertices is a yes-instance (its identity
moves every vertex vacuously). The vertex count is binary, so a whole permutation of `Fin n` is
not a polynomial certificate; but an automorphism maps isolated vertices to isolated vertices,
and the isolated vertices can be permuted without fixed points unless there is exactly one of
them, so the automorphism on the non-isolated vertices (all named in the edge list) together
with that count check is one, and membership in NP holds for this encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
A. Lubiw, "Some NP-complete problems similar to graph isomorphism", SIAM Journal on Computing
10 (1981), 11-21, doi:10.1137/0210002 (original not available here; the abstract: "the problem of
determining whether a given graph has a fixed-point-free automorphism" is NP-complete);
A. Abiad, G. Coutinho, E. Juliano, V. F. dos Santos and S. Zeijlemaker, "Computing fixed point
free automorphisms of graphs", arXiv:2603.26006 (2026), Section 1 (the problem statement quoted
below, attributed to Lubiw).
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FixedPointFreeAutomorphism

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev FixedPointFreeAutomorphismInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : FixedPointFreeAutomorphismInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : FixedPointFreeAutomorphismInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- The graph has an automorphism that fixes no vertex. -/
def FixedPointFreeAutomorphismFeasible (i : FixedPointFreeAutomorphismInstance) : Prop :=
  ∃ f : Graph i ≃g Graph i, ∀ v, f v ≠ v

open Classical in
/-- FIXED-POINT-FREE AUTOMORPHISM as a decision problem over bitstrings. -/
noncomputable def fixedPointFreeAutomorphismDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FixedPointFreeAutomorphismInstance) x with
  | some i => decide (WellFormed i ∧ FixedPointFreeAutomorphismFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FixedPointFreeAutomorphism
