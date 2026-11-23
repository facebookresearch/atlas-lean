/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTEGRITY PRESERVING CUT is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982), 182-195,
doi:10.1016/0196-6774(82)90018-9, problem [5] INTEGRITY PRESERVING CUT (reference: M. Luby,
private communication; transformation from 3SAT);
P. van 't Hof, D. Paulusma and G. J. Woeginger, "Partitioning graphs into connected parts",
Theoretical Computer Science 410 (2009), 4834-4843, doi:10.1016/j.tcs.2009.06.028.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntegrityPreservingCut

/-!
# INTEGRITY PRESERVING CUT is NP-complete

INSTANCE: a graph `G = (V, E)` and disjoint subsets `U₁, U₂ ⊆ V`.
QUESTION: is there a partition of `V` into disjoint sets `V₁` and `V₂` such that, for each
`i ∈ {1, 2}`, `Uᵢ ⊆ Vᵢ` and the subgraph of `G` induced by `Vᵢ` is connected?
(Johnson's column, problem [5], citing Luby's unpublished proof, which was not available; van 't
Hof, Paulusma and Woeginger 2009 study the same problem as 2-DISJOINT CONNECTED SUBGRAPHS and
prove it NP-complete, even when `|U₁| = 2`.)

The graph is given by its vertex count `n` and a simple edge list, as the `SimpleGraph (Fin n)`
`Cslib.Complexity.Karp.edgeGraph n es`; `U₁` and `U₂` are lists of vertices. `V₂` is the
complement of `V₁`; "connected" is Mathlib's `SimpleGraph.Connected` of the induced subgraph,
which includes being nonempty.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of vertices, the edges, and the vertex lists `U₁` and `U₂`. -/
abbrev IntegrityPreservingCutInstance := ℕ × List (ℕ × ℕ) × List ℕ × List ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : IntegrityPreservingCutInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness: a simple edge list on the vertices `0, …, n - 1`, and `U₁`, `U₂` disjoint
sets of vertices. -/
def WellFormed (i : IntegrityPreservingCutInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (∀ u ∈ i.2.2.1, u < i.1) ∧ (∀ u ∈ i.2.2.2, u < i.1) ∧ ∀ u ∈ i.2.2.1, u ∉ i.2.2.2

/-- Some set `V₁` with complement `V₂` has `U₁ ⊆ V₁`, `U₂ ⊆ V₂`, and both induced subgraphs
connected. -/
def IntegrityPreservingCutFeasible (i : IntegrityPreservingCutInstance) : Prop :=
  ∃ V₁ : Finset (Fin i.1),
    (∀ v : Fin i.1, (v : ℕ) ∈ i.2.2.1 → v ∈ V₁) ∧
    (∀ v : Fin i.1, (v : ℕ) ∈ i.2.2.2 → v ∉ V₁) ∧
    ((Graph i).induce (V₁ : Set (Fin i.1))).Connected ∧
    ((Graph i).induce ((V₁ᶜ : Finset (Fin i.1)) : Set (Fin i.1))).Connected

open Classical in
/-- INTEGRITY PRESERVING CUT as a decision problem over bitstrings. -/
noncomputable def integrityPreservingCutDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntegrityPreservingCutInstance) x with
  | some i => decide (WellFormed i ∧ IntegrityPreservingCutFeasible i)
  | none => false

/-- **INTEGRITY PRESERVING CUT is NP-complete.** Source: Johnson (1982), problem [5]; van 't Hof,
Paulusma and Woeginger (2009). -/
public theorem_wanted integrityPreservingCut_npComplete :
    integrityPreservingCutDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L integrityPreservingCutDec

end MetaMathlibExt.Complexity.NPComplete.IntegrityPreservingCut
