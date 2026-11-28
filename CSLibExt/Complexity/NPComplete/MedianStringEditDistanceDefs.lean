/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MEDIAN STRING under the edit distance: definitions

Source:
C. de la Higuera and F. Casacuberta, "Topology of strings: median string is NP-complete",
Theoretical Computer Science 230 (2000), 39-48, doi:10.1016/S0304-3975(97)00240-5 (unbounded
alphabets);
F. Nicolas and E. Rivals, "Hardness results for the center and median string problems under
the weighted and unweighted edit distances", Journal of Discrete Algorithms 3 (2005), 390-415,
doi:10.1016/j.jda.2004.08.015 (bounded and binary alphabets).
-/
module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.EditDistance.Algorithm
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MedianStringEditDistance

/-- An instance: the alphabet size `|Σ|`, the strings `s₁, …, sₙ`, and the bound `K`. -/
abbrev MedianStringEditDistanceInstance := ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: the alphabet is nonempty, the list of strings is nonempty,
and every letter of every string lies in `Σ`. -/
def WellFormed (i : MedianStringEditDistanceInstance) : Prop :=
  0 < i.1 ∧ i.2.1 ≠ [] ∧ ∀ s ∈ i.2.1, ∀ a ∈ s, a < i.1

/-- Some string `t` over `Σ` has total edit distance at most `K` to the strings `sᵢ`. -/
def MedianStringEditDistanceFeasible (i : MedianStringEditDistanceInstance) : Prop :=
  ∃ t : List ℕ, (∀ a ∈ t, a < i.1) ∧
    (i.2.1.map fun s => (Cslib.Algorithms.Lean.editDistance t s).ret.distance).sum ≤ i.2.2

open Classical in
/-- MEDIAN STRING under the edit distance as a decision problem over bitstrings. -/
noncomputable def medianStringEditDistanceDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MedianStringEditDistanceInstance) x with
  | some i => decide (WellFormed i ∧ MedianStringEditDistanceFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MedianStringEditDistance
