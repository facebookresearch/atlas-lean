/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SECOND-ORDER COPELAND MANIPULATION (unique winner): definitions

Source:
J. J. Bartholdi III, C. A. Tovey and M. A. Trick, "The computational difficulty of manipulating
an election", Social Choice and Welfare 6 (1989), 227-241, doi:10.1007/BF00295861,
Section 4, Theorem 3 (Existence of a Winning Preference for second-order Copeland).
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Sets
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.GameTheory.SocialChoice.CondorcetCycle
public import MathlibExt.GameTheory.SocialChoice.VotingRules

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SecondOrderCopelandManipulation

open MathlibExt.GameTheory.SocialChoice.ArrowWanted (Profile)
open MathlibExt.GameTheory.SocialChoice.CondorcetCycle (MajorityPrefers)

/-- An instance: the candidates `C`, the sincere votes `V` (each listing the candidates from
most to least preferred), and the distinguished candidate `p`. -/
abbrev SecondOrderCopelandManipulationInstance := List ℕ × List (List ℕ) × ℕ

/-- Well-formedness of an instance: the candidates are distinct, every sincere vote is a
permutation of the candidates, and `p` is a candidate. -/
def WellFormed (i : SecondOrderCopelandManipulationInstance) : Prop :=
  i.1.Nodup ∧ (∀ v ∈ i.2.1, v.Perm i.1) ∧ i.2.2 ∈ i.1

/-- The candidates of an instance. -/
abbrev Candidate (i : SecondOrderCopelandManipulationInstance) : Type := {x : ℕ // x ∈ i.1}

open Classical in
/-- The Copeland score of `a`: the number of pairwise contests `a` wins minus the number it
loses. -/
noncomputable def copelandScore {Alt Voter : Type} [Fintype Alt] [Fintype Voter]
    (P : Profile Alt Voter) (a : Alt) : ℤ :=
  MathlibExt.GameTheory.SocialChoice.copelandScore P a

/-- The local Copeland score agrees with the standard Copeland score. -/
theorem copelandScore_eq {Alt Voter : Type} [Fintype Alt] [Fintype Voter]
    (P : Profile Alt Voter) (a : Alt) :
    copelandScore P a = MathlibExt.GameTheory.SocialChoice.copelandScore P a :=
  rfl

open Classical in
/-- The second-order Copeland score of `a`: the sum of the Copeland scores of the candidates
that `a` defeats. -/
noncomputable def secondOrderScore {Alt Voter : Type} [Fintype Alt] [Fintype Voter]
    (P : Profile Alt Voter) (a : Alt) : ℤ :=
  MathlibExt.GameTheory.SocialChoice.secondOrderCopelandScore P a

/-- The local second-order score agrees with the standard second-order score. -/
theorem secondOrderScore_eq {Alt Voter : Type} [Fintype Alt] [Fintype Voter]
    (P : Profile Alt Voter) (a : Alt) :
    secondOrderScore P a = MathlibExt.GameTheory.SocialChoice.secondOrderCopelandScore P a :=
  rfl

/-- `p` is the unique second-order Copeland winner: every other candidate has a smaller
Copeland score, or the same Copeland score and a smaller second-order score. -/
def IsUniqueWinner {Alt Voter : Type} [Fintype Alt] [Fintype Voter]
    (P : Profile Alt Voter) (p : Alt) : Prop :=
  ∀ q, q ≠ p → copelandScore P q < copelandScore P p ∨
    (copelandScore P q = copelandScore P p ∧ secondOrderScore P q < secondOrderScore P p)

/-- `p` is the unique winner exactly when `p` is the only standard second-order Copeland winner. -/
theorem isUniqueWinner_iff_secondOrderCopelandWinners_eq_singleton
    {Alt Voter : Type} [Fintype Alt] [Fintype Voter] [DecidableEq Alt]
    (P : Profile Alt Voter) (p : Alt) :
    IsUniqueWinner P p ↔
      MathlibExt.GameTheory.SocialChoice.secondOrderCopelandWinners P = {p} := by
  constructor
  · intro h
    unfold IsUniqueWinner at h
    simp only [copelandScore_eq, secondOrderScore_eq] at h
    unfold MathlibExt.GameTheory.SocialChoice.secondOrderCopelandWinners
      MathlibExt.GameTheory.SocialChoice.IsSecondOrderCopelandWinner
    apply Finset.ext
    intro q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hq
      by_contra hne
      have hq_p := hq p
      have hp_q := h q hne
      rcases hp_q with hlt | ⟨heq, hlt2⟩
      · rcases hq_p with hlt' | ⟨heq', _⟩
        · omega
        · omega
      · rcases hq_p with hlt' | ⟨heq', hle'⟩
        · omega
        · omega
    · intro heq
      rw [heq]
      intro b
      by_cases hb : b = p
      · rw [hb]
        right
        exact ⟨rfl, le_rfl⟩
      · have hb' := h b hb
        rcases hb' with hlt | ⟨heq2, hlt2⟩
        · left; exact hlt
        · right; exact ⟨heq2, le_of_lt hlt2⟩
  · intro h
    unfold IsUniqueWinner
    simp only [copelandScore_eq, secondOrderScore_eq]
    intro q hne
    have hp_mem : p ∈ MathlibExt.GameTheory.SocialChoice.secondOrderCopelandWinners P := by
      rw [h]
      exact Finset.mem_singleton_self p
    have hq_nmem : q ∉ MathlibExt.GameTheory.SocialChoice.secondOrderCopelandWinners P := by
      rw [h]
      simp [hne]
    unfold MathlibExt.GameTheory.SocialChoice.secondOrderCopelandWinners
      MathlibExt.GameTheory.SocialChoice.IsSecondOrderCopelandWinner at hp_mem hq_nmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp_mem hq_nmem
    have hp_q := hp_mem q
    rcases hp_q with hlt | ⟨heq, hle⟩
    · left; exact hlt
    · rcases lt_or_eq_of_le hle with hlt2 | heq2
      · right; exact ⟨heq, hlt2⟩
      · exfalso
        apply hq_nmem
        intro b
        have hb := hp_mem b
        rcases hb with hltb | ⟨heqb, hleb⟩
        · left
          omega
        · right
          constructor
          · omega
          · omega

/-- Some order of the manipulator (the last voter) makes `p` the unique winner, the other
voters voting their sincere orders: voter `k` prefers `a` to `b` exactly when `a` comes before
`b` in the `k`-th vote. -/
def SecondOrderCopelandManipulationFeasible
    (i : SecondOrderCopelandManipulationInstance) : Prop :=
  ∃ hp : i.2.2 ∈ i.1, ∃ P : Profile (Candidate i) (Fin (i.2.1.length + 1)),
    (∀ k : Fin i.2.1.length, ∀ a b : Candidate i,
      (P k.castSucc).lt a b ↔ (i.2.1.get k).idxOf a.1 < (i.2.1.get k).idxOf b.1) ∧
    IsUniqueWinner P ⟨i.2.2, hp⟩

open Classical in
/-- SECOND-ORDER COPELAND MANIPULATION as a decision problem over bitstrings. -/
noncomputable def secondOrderCopelandManipulationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SecondOrderCopelandManipulationInstance) x with
  | some i => decide (WellFormed i ∧ SecondOrderCopelandManipulationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SecondOrderCopelandManipulation
