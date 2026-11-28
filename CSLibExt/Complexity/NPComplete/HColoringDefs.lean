/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# H-COLORING: definitions

Source:
P. Hell and J. Nešetřil, "On the complexity of H-coloring", Journal of Combinatorial Theory,
Series B 48 (1990), 92-110, doi:10.1016/0095-8956(90)90132-J.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Complexity.NPComplete.GraphHomomorphismDefs
public import Mathlib.Combinatorics.SimpleGraph.Bipartite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HColoring

/-- An instance: vertex count `n` of `G` (vertices `Fin n`) and the edge list of `G`. -/
abbrev HColoringInstance := ℕ × List (ℕ × ℕ)

/-- The GRAPH HOMOMORPHISM instance with source `G = i` and target `H = (m, hs)`. -/
def withPattern (m : ℕ) (hs : List (ℕ × ℕ)) (i : HColoringInstance) :
    GraphHomomorphism.GraphHomomorphismInstance :=
  (i.1, i.2, m, hs)

/-- A pattern `H = (m, hs)` for which the theorem is stated: `hs` is a simple edge list on
`Fin m` (no duplicate edges in either orientation, no self-loops, endpoints in range), and `H`
is not bipartite. -/
def ValidPattern (m : ℕ) (hs : List (ℕ × ℕ)) : Prop :=
  (hs.Nodup ∧ ∀ e ∈ hs, e.1 < m ∧ e.2 < m ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ hs) ∧
    ¬ (Cslib.Complexity.Karp.edgeGraph m hs).IsBipartite

open Classical in
/-- H-COLORING for the fixed pattern `H = (m, hs)` as a decision problem over bitstrings. -/
noncomputable def hColoringDec (m : ℕ) (hs : List (ℕ × ℕ)) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := HColoringInstance) x with
  | some i => decide (GraphHomomorphism.WellFormed (withPattern m hs i) ∧
      GraphHomomorphism.GraphHomomorphismFeasible (withPattern m hs i))
  | none => false

end MetaMathlibExt.Complexity.NPComplete.HColoring
