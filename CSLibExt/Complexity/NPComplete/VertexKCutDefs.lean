/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# VERTEX K-CUT: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
problem MINIMUM VERTEX K-CUT, citing N. Garg, V. V. Vazirani and M. Yannakakis, "Multiway
cuts in directed and node weighted graphs", Proc. 21st ICALP, Lecture Notes in Computer Science
820 (1994), 487-498, doi:10.1007/3-540-58201-0_92; journal version: "Multiway cuts in node
weighted graphs", Journal of Algorithms 50 (2004), 49-61, doi:10.1016/S0196-6774(03)00111-1;
M. Johnson, B. Martin, S. Pandey, D. Paulusma, S. Smith and E. J. van Leeuwen, "Edge Multiway
Cut and Node Multiway Cut are hard for planar subcubic graphs", Algorithmica 88 (2026),
article 66, doi:10.1007/s00453-026-01412-5 (NODE MULTIWAY CUT, the special case in which the
pairs are all pairs of a terminal set `T`, every weight is `1` and `C ⊆ V \ T`, is NP-complete,
even for planar graphs of maximum degree 3; NP-completeness for `|T| = 3` is credited there to
Garg, Vazirani and Yannakakis).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.VertexKCut

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), edge list, the list of pairs
`(sᵢ, tᵢ)`, the vertex weights `w` (indexed by vertex), and the bound `K`. -/
abbrev VertexKCutInstance := ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) × List ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : VertexKCutInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), every pair has both
vertices below `n`, there is one weight per vertex, and `K` is positive. -/
def WellFormed (i : VertexKCutInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (∀ p ∈ i.2.2.1, p.1 < i.1 ∧ p.2 < i.1) ∧ i.2.2.2.1.length = i.1 ∧ 0 < i.2.2.2.2

/-- A vertex k-cut of weight at most `K`: a set `C` of vertices containing no special vertex, of
total weight at most `K`, such that in the subgraph of `G` induced on the vertices outside `C`
(`SimpleGraph.induce`) the terminal of every pair is not reachable from its source. -/
def VertexKCutFeasible (i : VertexKCutInstance) : Prop :=
  ∃ C : Finset (Fin i.1),
    (∀ v ∈ C, ∀ p ∈ i.2.2.1, p.1 ≠ (v : ℕ) ∧ p.2 ≠ (v : ℕ)) ∧
      ∑ v ∈ C, i.2.2.2.1.getD v 0 ≤ i.2.2.2.2 ∧
        ∀ p ∈ i.2.2.1, ∀ hs : p.1 < i.1, ∀ ht : p.2 < i.1,
          ∀ hsC : (⟨p.1, hs⟩ : Fin i.1) ∈ ((C : Set (Fin i.1))ᶜ),
            ∀ htC : (⟨p.2, ht⟩ : Fin i.1) ∈ ((C : Set (Fin i.1))ᶜ),
              ¬ ((Graph i).induce ((C : Set (Fin i.1))ᶜ)).Reachable
                ⟨⟨p.1, hs⟩, hsC⟩ ⟨⟨p.2, ht⟩, htC⟩

open Classical in
/-- VERTEX K-CUT as a decision problem over bitstrings. -/
noncomputable def vertexKCutDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := VertexKCutInstance) x with
  | some i => decide (WellFormed i ∧ VertexKCutFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.VertexKCut
