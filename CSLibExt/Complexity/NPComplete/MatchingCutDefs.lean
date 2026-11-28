/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MATCHING CUT: definitions

Source:
V. Chvátal, "Recognizing decomposable graphs", Journal of Graph Theory 8(1) (1984), 51-53,
doi:10.1002/jgt.3190080106 (recognizing decomposable graphs is NP-complete, already for graphs
of maximum degree 4).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MatchingCut

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list. -/
abbrev MatchingCutInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : MatchingCutInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: a simple edge list on `Fin n` (no repeated edge, no loop,
no reversed copy). -/
def WellFormed (i : MatchingCutInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- `c` decomposes `G` (`true` for red, `false` for blue): both colors occur, and any two
neighbors of a vertex `v` that have a color different from that of `v` are equal. -/
def IsDecomposition {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → Bool) : Prop :=
  (∃ v, c v = true) ∧ (∃ v, c v = false) ∧
    ∀ v w₁ w₂, G.Adj v w₁ → G.Adj v w₂ → c w₁ ≠ c v → c w₂ ≠ c v → w₁ = w₂

/-- The graph is decomposable (has a matching cut). -/
def MatchingCutFeasible (i : MatchingCutInstance) : Prop :=
  ∃ c : Fin i.1 → Bool, IsDecomposition (Graph i) c

open Classical in
/-- MATCHING CUT as a decision problem over bitstrings. -/
noncomputable def matchingCutDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MatchingCutInstance) x with
  | some i => decide (WellFormed i ∧ MatchingCutFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MatchingCut
