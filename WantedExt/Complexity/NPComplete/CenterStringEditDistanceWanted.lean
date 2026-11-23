/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CENTER STRING under the edit distance is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Algorithms.Lean.DynamicProgramming.EditDistance.Algorithm
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CenterStringEditDistance

/-!
# CENTER STRING under the edit distance is NP-complete

INSTANCE: a finite alphabet `Σ`, a nonempty finite list of strings `s₁, …, sₙ` over `Σ`, and a
non-negative integer `K`.
QUESTION: is there a string `t` over `Σ` with `d_E(t, sᵢ) ≤ K` for every `i`, where `d_E` is
the unit-cost edit (Levenshtein) distance, the smallest number of single-letter deletions,
insertions and substitutions transforming one string into the other? Equivalently, is the
radius `R(W) = inf_{γ ∈ Σ*} max_{w ∈ W} d_E(γ, w)` of `W = {s₁, …, sₙ}` at most `K`?

The alphabet is `Σ = {0, …, |Σ| - 1}`, given by its size, and strings are lists of letters.
The edit distance is CSLib's unit-cost Levenshtein distance
`(Cslib.Algorithms.Lean.editDistance x y).ret.distance`, which
`Cslib.Algorithms.Lean.editDistance_minimal` and `Cslib.Algorithms.Lean.editDistance_script_cost`
identify with the least cost of an edit script of deletions, insertions and substitutions.

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

/-- **CENTER STRING under the edit distance is NP-complete.** Source: Nicolas and Rivals
(2003, 2005). -/
public theorem_wanted centerStringEditDistance_npComplete :
    centerStringEditDistanceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L centerStringEditDistanceDec

end MetaMathlibExt.Complexity.NPComplete.CenterStringEditDistance
