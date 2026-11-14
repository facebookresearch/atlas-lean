/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MEDIAN STRING under the edit distance is NP-complete

Source:
C. de la Higuera and F. Casacuberta, "Topology of strings: median string is NP-complete",
Theoretical Computer Science 230 (2000), 39-48, doi:10.1016/S0304-3975(97)00240-5 (unbounded
alphabets);
F. Nicolas and E. Rivals, "Hardness results for the center and median string problems under
the weighted and unweighted edit distances", Journal of Discrete Algorithms 3 (2005), 390-415,
doi:10.1016/j.jda.2004.08.015 (bounded and binary alphabets).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Algorithms.Lean.DynamicProgramming.EditDistance.Algorithm
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MedianStringEditDistance

/-!
# MEDIAN STRING under the edit distance is NP-complete

INSTANCE: a finite alphabet `Σ`, a nonempty finite list of strings `s₁, …, sₙ` over `Σ`, and a
non-negative integer `K`.
QUESTION: is there a string `t` over `Σ` with `∑ᵢ d_E(t, sᵢ) ≤ K`, where `d_E` is the
unit-cost edit (Levenshtein) distance, the smallest number of single-letter deletions,
insertions and substitutions transforming one string into the other? Equivalently, is the sum
of the edit distances from a median string of `{s₁, …, sₙ}` to the given strings at most `K`?

The alphabet is `Σ = {0, …, |Σ| - 1}`, given by its size, and strings are lists of letters.
The edit distance is CSLib's unit-cost Levenshtein distance
`(Cslib.Algorithms.Lean.editDistance x y).ret.distance`, which
`Cslib.Algorithms.Lean.editDistance_minimal` and `Cslib.Algorithms.Lean.editDistance_script_cost`
identify with the least cost of an edit script of deletions, insertions and substitutions.
Every string `sᵢ` counts with its multiplicity in the list.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **MEDIAN STRING under the edit distance is NP-complete.** Source: de la Higuera and
Casacuberta (2000); Nicolas and Rivals (2005). -/
public theorem_wanted medianStringEditDistance_npComplete :
    medianStringEditDistanceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L medianStringEditDistanceDec

end MetaMathlibExt.Complexity.NPComplete.MedianStringEditDistance
