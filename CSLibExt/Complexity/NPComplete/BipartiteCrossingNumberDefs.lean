/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BIPARTITE CROSSING NUMBER: definitions

Source:
M. R. Garey and D. S. Johnson, "Crossing number is NP-complete", SIAM Journal on Algebraic and
Discrete Methods 4(3) (1983), 312-316, doi:10.1137/0604033 (the bipartite crossing number
problem for bipartite multigraphs, the intermediate step of the proof, by a transformation from
OPTIMAL LINEAR ARRANGEMENT [GT42]);
C. Buchheim, M. Chimani, C. Gutwenger, M. Jünger and P. Mutzel, "Crossings and planarization",
in R. Tamassia (ed.), *Handbook of Graph Drawing and Visualization*, CRC Press (2013), chapter 2,
Section 2.3.1, Lemma 2.1 (statement of the problem and a reproduction of the proof).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.OneSidedCrossingMinimizationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BipartiteCrossingNumber

open OneSidedCrossingMinimization (crossings)

/-- An instance: the vertices of `V₁`, the vertices of `V₂`, the edges `(u, w)` (repetitions
allowed), and the bound `K`. -/
abbrev BipartiteCrossingNumberInstance := List ℕ × List ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: `V₁` and `V₂` are listed without repetition, and every edge
joins a vertex of `V₁` to a vertex of `V₂`. -/
def WellFormed (i : BipartiteCrossingNumberInstance) : Prop :=
  i.1.Nodup ∧ i.2.1.Nodup ∧ ∀ e ∈ i.2.2.1, e.1 ∈ i.1 ∧ e.2 ∈ i.2.1

/-- Some order of `V₁` and some order of `V₂` give a two-sided drawing with at most `K`
crossings. -/
def BipartiteCrossingNumberFeasible (i : BipartiteCrossingNumberInstance) : Prop :=
  ∃ order₁ order₂ : List ℕ, order₁.Perm i.1 ∧ order₂.Perm i.2.1 ∧
    crossings order₁ order₂ i.2.2.1 ≤ i.2.2.2

open Classical in
/-- BIPARTITE CROSSING NUMBER as a decision problem over bitstrings. -/
noncomputable def bipartiteCrossingNumberDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BipartiteCrossingNumberInstance) x with
  | some i => decide (WellFormed i ∧ BipartiteCrossingNumberFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BipartiteCrossingNumber
