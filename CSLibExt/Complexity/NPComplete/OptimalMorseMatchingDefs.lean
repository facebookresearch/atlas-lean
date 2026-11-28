/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPTIMAL MORSE MATCHING: definitions

Source:
M. Joswig and M. E. Pfetsch, "Computing optimal Morse matchings", SIAM Journal on Discrete
Mathematics 20 (2006), 11-25, doi:10.1137/S0895480104445885 (arXiv:math/0408331), Section 4;
Ö. Eğecioğlu and T. F. Gonzalez, "A computationally intractable problem on simplicial
complexes", Computational Geometry 6 (1996), 85-98, doi:10.1016/0925-7721(95)00015-1.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OptimalMorseMatching

/-- An instance: the faces of the complex (strictly increasing vertex lists) and the bound `c`. -/
abbrev OptimalMorseMatchingInstance := List (List ℕ) × ℕ

/-- Well-formedness of an instance: every face is a nonempty strictly increasing list, no face
is listed twice, and every nonempty sublist of a face is a face. -/
def WellFormed (i : OptimalMorseMatchingInstance) : Prop :=
  (∀ F ∈ i.1, F ≠ [] ∧ F.Pairwise (· < ·)) ∧ i.1.Nodup ∧
    ∀ F ∈ i.1, ∀ G : List ℕ, G.Sublist F → G ≠ [] → G ∈ i.1

/-- `F ≺ G`: the face `F` is a facet of the face `G` (for strictly increasing lists). -/
def Covers (F G : List ℕ) : Prop :=
  F.Sublist G ∧ G.length = F.length + 1

/-- Some Morse matching (pairs `F ≺ G` of faces, each face in at most one pair, acyclic as
witnessed by a ranking) leaves at most `c` faces critical. -/
def OptimalMorseMatchingFeasible (i : OptimalMorseMatchingInstance) : Prop :=
  ∃ M : List (List ℕ × List ℕ),
    (∀ p ∈ M, p.1 ∈ i.1 ∧ p.2 ∈ i.1 ∧ Covers p.1 p.2) ∧ (M.map Prod.fst ++ M.map Prod.snd).Nodup ∧
    (∃ r : List ℕ → ℕ, ∀ F ∈ i.1, ∀ G ∈ i.1, Covers F G →
      ((F, G) ∈ M → r G < r F) ∧ ((F, G) ∉ M → r F < r G)) ∧
    (i.1.filter fun F => F ∉ M.map Prod.fst ∧ F ∉ M.map Prod.snd).length ≤ i.2

open Classical in
/-- OPTIMAL MORSE MATCHING as a decision problem over bitstrings. -/
noncomputable def optimalMorseMatchingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OptimalMorseMatchingInstance) x with
  | some i => decide (WellFormed i ∧ OptimalMorseMatchingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.OptimalMorseMatching
