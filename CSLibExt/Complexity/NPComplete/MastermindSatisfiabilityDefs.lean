/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MASTERMIND SATISFIABILITY: definitions

Source:
J. Stuckman and G.-Q. Zhang, "Mastermind is NP-complete", INFOCOMP Journal of Computer
Science 5(2) (2006), 25-28, arXiv:cs/0512049 (Definition 2.1, Section 2.1, Theorem 2.1).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MastermindSatisfiability

/-- An instance `(κ, ℓ, G)`: the number of colors `κ`, the code length `ℓ`, and the scored
guesses `(g, b_g, w_g)`, a guess `g` with its black-peg count `b_g` and white-peg count
`w_g`. -/
abbrev MastermindSatisfiabilityInstance := ℕ × ℕ × List (List ℕ × ℕ × ℕ)

/-- The black pegs of guess `g` against code `s`: `b = #{i | gᵢ = sᵢ}`. -/
def blackPegs {ℓ κ : ℕ} (g : List ℕ) (s : Fin ℓ → Fin κ) : ℕ :=
  (Finset.univ.filter fun i : Fin ℓ => g.getD i 0 = s i).card

/-- The color matches of guess `g` against code `s`, irrespective of position:
`w = ∑ⱼ min(#{i | gᵢ = j}, #{i | sᵢ = j})`, the sum over the colors `j`. -/
def colorMatches {ℓ κ : ℕ} (g : List ℕ) (s : Fin ℓ → Fin κ) : ℕ :=
  ∑ j : Fin κ, min (Finset.univ.filter fun i : Fin ℓ => g.getD i 0 = j).card
    (Finset.univ.filter fun i : Fin ℓ => s i = j).card

/-- The Mastermind score `ρ(g, s) = (b, w - b)`: black pegs, then white pegs. For a guess
with colors below `κ` the subtraction does not truncate, since each position counted by
`b` is also counted by `w`. -/
def score {ℓ κ : ℕ} (g : List ℕ) (s : Fin ℓ → Fin κ) : ℕ × ℕ :=
  (blackPegs g s, colorMatches g s - blackPegs g s)

/-- Well-formedness of an instance `(κ, ℓ, G)`: `κ > 1`, every guess is a tuple of `ℓ` colors
below `κ`, and the guesses are distinct (`G` is a set, with one score per guess). -/
def WellFormed (i : MastermindSatisfiabilityInstance) : Prop :=
  1 < i.1 ∧ (i.2.2.map Prod.fst).Nodup ∧
    ∀ q ∈ i.2.2, q.1.length = i.2.1 ∧ ∀ c ∈ q.1, c < i.1

/-- Some code `s ∈ [κ]^ℓ` has score `ρ(g, s) = (b_g, w_g)` for every scored guess. -/
def MastermindSatisfiabilityFeasible (i : MastermindSatisfiabilityInstance) : Prop :=
  ∃ s : Fin i.2.1 → Fin i.1, ∀ q ∈ i.2.2, score q.1 s = q.2

open Classical in
/-- MASTERMIND SATISFIABILITY as a decision problem over bitstrings. -/
noncomputable def mastermindSatisfiabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MastermindSatisfiabilityInstance) x with
  | some i => decide (WellFormed i ∧ MastermindSatisfiabilityFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MastermindSatisfiability
