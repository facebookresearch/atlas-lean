/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHAIN GRAPH COMPLETION: definitions

Source:
M. Yannakakis, "Computing the minimum fill-in is NP-complete", SIAM Journal on Algebraic and
Discrete Methods 2 (1981), 77-79, doi:10.1137/0602010;
A. Natanzon, R. Shamir and R. Sharan, "Complexity classification of some edge modification
problems", Discrete Applied Mathematics 113 (2001), 109-128,
doi:10.1016/S0166-218X(00)00391-7, Section 3.1.
-/
module

public import Mathlib.Data.Finset.Card
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChainGraphCompletion

/-- An instance: the side sizes `p = |P|` and `q = |Q|`, the edges `(a, b)` with `a < p` and
`b < q`, and the bound `K`. -/
abbrev ChainGraphCompletionInstance := ℕ × ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: the edges are distinct pairs `(a, b)` with `a < p` and
`b < q`. -/
def WellFormed (i : ChainGraphCompletionInstance) : Prop :=
  i.2.2.1.Nodup ∧ ∀ e ∈ i.2.2.1, e.1 < i.1 ∧ e.2 < i.2.1

/-- The edge set `E ⊆ P × Q` of the instance. -/
def Edges (i : ChainGraphCompletionInstance) : Finset (Fin i.1 × Fin i.2.1) :=
  Finset.univ.filter fun e => ((e.1 : ℕ), (e.2 : ℕ)) ∈ i.2.2.1

/-- The bipartite graph with edge set `F ⊆ P × Q` is a chain graph: for any two vertices
`u, v ∈ P`, `N(u) ⊆ N(v)` or `N(v) ⊆ N(u)`. -/
def IsChainGraph {P Q : Type*} (F : Finset (P × Q)) : Prop :=
  ∀ u v : P, (∀ w, (u, w) ∈ F → (v, w) ∈ F) ∨ (∀ w, (v, w) ∈ F → (u, w) ∈ F)

/-- Adding at most `K` edges between `P` and `Q` gives a chain graph. -/
def ChainGraphCompletionFeasible (i : ChainGraphCompletionInstance) : Prop :=
  ∃ F : Finset (Fin i.1 × Fin i.2.1), Edges i ⊆ F ∧ (F \ Edges i).card ≤ i.2.2.2 ∧
    IsChainGraph F

open Classical in
/-- CHAIN GRAPH COMPLETION as a decision problem over bitstrings. -/
noncomputable def chainGraphCompletionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ChainGraphCompletionInstance) x with
  | some i => decide (WellFormed i ∧ ChainGraphCompletionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ChainGraphCompletion
