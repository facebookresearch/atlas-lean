/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CENTER STRING under the edit distance: definitions

Source:
F. Nicolas and E. Rivals, "Complexities of the centre and median string problems",
Combinatorial Pattern Matching (CPM 2003), Lecture Notes in Computer Science 2676 (2003),
315-327, doi:10.1007/3-540-44888-8_23 (Definition 2 and Theorem 4: the centre string problem
is NP-complete even if the alphabet is binary);
F. Nicolas and E. Rivals, "Hardness results for the center and median string problems under
the weighted and unweighted edit distances", Journal of Discrete Algorithms 3 (2005), 390-415,
doi:10.1016/j.jda.2004.08.015 (journal version).
-/
module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.EditDistance.Algorithm
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CenterStringEditDistance

/-- An instance: the alphabet size `|Σ|`, the strings `s₁, …, sₙ`, and the bound `K`. -/
abbrev CenterStringEditDistanceInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: the alphabet is nonempty, the list of strings is nonempty,
and every letter of every string lies in `Σ`. -/
def WellFormed (i : CenterStringEditDistanceInstance) : Prop :=
  0 < i.1 ∧ i.2.1 ≠ [] ∧ ∀ s ∈ i.2.1, ∀ a ∈ s, a < i.1

/-- Some string `t` over `Σ` is within edit distance `K` of every `sᵢ`. -/
def CenterStringEditDistanceFeasible (i : CenterStringEditDistanceInstance) : Prop :=
  ∃ t : List ℕ, (∀ a ∈ t, a < i.1) ∧
    ∀ s ∈ i.2.1, (Cslib.Algorithms.Lean.editDistance t s).ret.distance ≤ i.2.2

open Classical in
/-- CENTER STRING under the edit distance as a decision problem over bitstrings. -/
noncomputable def centerStringEditDistanceDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CenterStringEditDistanceInstance) x with
  | some i => decide (WellFormed i ∧ CenterStringEditDistanceFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CenterStringEditDistance
