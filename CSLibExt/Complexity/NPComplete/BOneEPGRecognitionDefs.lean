/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# B₁-EPG GRAPH RECOGNITION: definitions

Source:
D. Heldt, K. Knauer and T. Ueckerdt, "Edge-intersection graphs of grid paths: the
bend-number", Discrete Applied Mathematics 167 (2014), 144-162,
doi:10.1016/j.dam.2013.10.035, Section 7 (arXiv:1009.2861).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.BkVPGRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BOneEPGRecognition

open BkVPGRecognition (BkVPGInstance Graph IsGridPath bends)

/-- The grid paths `P` and `Q` have a grid edge in common: some pair of consecutive points of
`P` is a pair of consecutive points of `Q`, in either order. -/
def SharesGridEdge (P Q : List (ℕ × ℕ)) : Prop :=
  ∃ p q : ℕ × ℕ, (p, q) ∈ P.zip P.tail ∧ ((p, q) ∈ Q.zip Q.tail ∨ (q, p) ∈ Q.zip Q.tail)

/-- `G` is a `B₁`-EPG (single-bend) graph: there are grid paths with at most one bend, one per
vertex, such that two distinct vertices are adjacent exactly when their paths share a grid
edge. -/
def IsBOneEPG {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ P : Fin n → List (ℕ × ℕ), (∀ v, IsGridPath (P v) ∧ bends (P v) ≤ 1) ∧
    ∀ u v, u ≠ v → (G.Adj u v ↔ SharesGridEdge (P u) (P v))

/-- The graph of the instance is a `B₁`-EPG graph. -/
def BOneEPGRecognitionFeasible (i : BkVPGInstance) : Prop :=
  IsBOneEPG (Graph i)

open Classical in
/-- `B₁`-EPG GRAPH RECOGNITION as a decision problem over bitstrings. -/
noncomputable def bOneEPGRecognitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BkVPGInstance) x with
  | some i => decide (BkVPGRecognition.WellFormed i ∧ BOneEPGRecognitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BOneEPGRecognition
