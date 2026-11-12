/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.SocialChoice.Arrow
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Defs.Unbundled
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Condorcet paradox: a majority cycle (Atlas AP03.T01)

Voters have strict total preferences over alternatives (the shared Atlas encoding
`MathlibExt.Order.StrictTotalOrder`, as in Arrow's theorem). Alternative `a` beats
`b` by pairwise majority when strictly more than half of the voters strictly
prefer `a` to `b`. Pairwise majority need not be transitive: three voters with
cyclic rankings over three alternatives produce a majority cycle, and then no
alternative is a Condorcet winner.
-/

@[expose] public section

namespace MathlibExt.GameTheory.SocialChoice.CondorcetCycle

open MathlibExt.GameTheory.SocialChoice.ArrowWanted

open Classical in
/-- The voters who strictly prefer `a` to `b` in profile `P`. -/
noncomputable def supporters {Alt Voter : Type*} [Fintype Voter] (P : Profile Alt Voter)
    (a b : Alt) : Finset Voter :=
  Finset.univ.filter fun i => MathlibExt.Order.StrictTotalOrder.lt (P i) a b

/-- `a` beats `b` by pairwise majority: strictly more than half of the voters
strictly prefer `a` to `b`. -/
def MajorityPrefers {Alt Voter : Type*} [Fintype Voter] (P : Profile Alt Voter)
    (a b : Alt) : Prop :=
  Fintype.card Voter < 2 * (supporters P a b).card

/-- A majority cycle `a ≻ b ≻ c ≻ a` under pairwise majority. -/
def IsMajorityCycle {Alt Voter : Type*} [Fintype Voter] (P : Profile Alt Voter)
    (a b c : Alt) : Prop :=
  MajorityPrefers P a b ∧ MajorityPrefers P b c ∧ MajorityPrefers P c a

/-- Rank of alternative `a` in voter `i`'s cyclic ranking: voter `i` ranks `i` first,
then `i + 1`, then `i + 2` (mod 3). -/
def crank (i a : Fin 3) : ℕ := (a.val + 3 - i.val) % 3

/-- Each voter's cyclic rank is injective (checked by `decide`). -/
theorem crank_injective_all : ∀ (i a b : Fin 3), crank i a = crank i b → a = b := by
  decide

/-- Each voter's cyclic rank is injective. -/
theorem crank_injective (i : Fin 3) : Function.Injective (crank i) :=
  fun _ _ h => crank_injective_all i _ _ h

/-- Voter `i`'s strict preference: `a` is preferred to `b` iff `a` has a smaller cyclic rank. -/
def cycOrder (i : Fin 3) : StrictTotalOrder (Fin 3) where
  lt := fun a b => crank i a < crank i b
  irrefl := fun a => Nat.lt_irrefl _
  trans := fun h1 h2 => Nat.lt_trans h1 h2
  total := fun {a b} hne => by
    have hinj := crank_injective i
    have hRne : crank i a ≠ crank i b := fun h => hne (hinj h)
    exact lt_or_gt_of_ne hRne

/-- The Condorcet profile: voter `i` ranks `i ≻ i + 1 ≻ i + 2` (mod 3). -/
def condorcetProfile : Profile (Fin 3) (Fin 3) := fun i => cycOrder i

/-- In the Condorcet profile, voters `0` and `2` prefer `0` to `1`. -/
theorem condorcet_sup01 : supporters condorcetProfile 0 1 = {0, 2} := by
  ext i
  fin_cases i <;> simp [supporters, condorcetProfile, cycOrder, crank, Finset.mem_filter]

/-- In the Condorcet profile, voters `0` and `1` prefer `1` to `2`. -/
theorem condorcet_sup12 : supporters condorcetProfile 1 2 = {0, 1} := by
  ext i
  fin_cases i <;> simp [supporters, condorcetProfile, cycOrder, crank, Finset.mem_filter]

/-- In the Condorcet profile, voters `1` and `2` prefer `2` to `0`. -/
theorem condorcet_sup20 : supporters condorcetProfile 2 0 = {1, 2} := by
  ext i
  fin_cases i <;> simp [supporters, condorcetProfile, cycOrder, crank, Finset.mem_filter]

/-- In the Condorcet profile, only voter `0` prefers `0` to `2`. -/
theorem condorcet_sup02 : supporters condorcetProfile 0 2 = {0} := by
  ext i
  fin_cases i <;> simp [supporters, condorcetProfile, cycOrder, crank, Finset.mem_filter]

/-- In the Condorcet profile, only voter `1` prefers `1` to `0`. -/
theorem condorcet_sup10 : supporters condorcetProfile 1 0 = {1} := by
  ext i
  fin_cases i <;> simp [supporters, condorcetProfile, cycOrder, crank, Finset.mem_filter]

/-- Two voters prefer `0` to `1`. -/
theorem condorcet_card01 : (supporters condorcetProfile 0 1).card = 2 := by
  rw [condorcet_sup01]; decide

/-- Two voters prefer `1` to `2`. -/
theorem condorcet_card12 : (supporters condorcetProfile 1 2).card = 2 := by
  rw [condorcet_sup12]; decide

/-- Two voters prefer `2` to `0`. -/
theorem condorcet_card20 : (supporters condorcetProfile 2 0).card = 2 := by
  rw [condorcet_sup20]; decide

/-- One voter prefers `0` to `2`. -/
theorem condorcet_card02 : (supporters condorcetProfile 0 2).card = 1 := by
  rw [condorcet_sup02]; decide

/-- One voter prefers `1` to `0`. -/
theorem condorcet_card10 : (supporters condorcetProfile 1 0).card = 1 := by
  rw [condorcet_sup10]; decide

/-- `0` beats `1` by majority in the Condorcet profile. -/
theorem condorcet_maj01 : MajorityPrefers condorcetProfile 0 1 := by
  unfold MajorityPrefers; rw [condorcet_card01]; simp [Fintype.card_fin]

/-- `1` beats `2` by majority in the Condorcet profile. -/
theorem condorcet_maj12 : MajorityPrefers condorcetProfile 1 2 := by
  unfold MajorityPrefers; rw [condorcet_card12]; simp [Fintype.card_fin]

/-- `2` beats `0` by majority in the Condorcet profile. -/
theorem condorcet_maj20 : MajorityPrefers condorcetProfile 2 0 := by
  unfold MajorityPrefers; rw [condorcet_card20]; simp [Fintype.card_fin]

/-- `0` does not beat `2` by majority in the Condorcet profile. -/
theorem condorcet_nmaj02 : ¬ MajorityPrefers condorcetProfile 0 2 := by
  unfold MajorityPrefers; rw [condorcet_card02]; simp [Fintype.card_fin]

/-- `1` does not beat `0` by majority in the Condorcet profile. -/
theorem condorcet_nmaj10 : ¬ MajorityPrefers condorcetProfile 1 0 := by
  unfold MajorityPrefers; rw [condorcet_card10]; simp [Fintype.card_fin]

/-- The Condorcet profile has the majority cycle `0 ≻ 1 ≻ 2 ≻ 0`. -/
theorem condorcet_cycle : IsMajorityCycle condorcetProfile 0 1 2 :=
  ⟨condorcet_maj01, condorcet_maj12, condorcet_maj20⟩

/-- **Condorcet paradox.** Some profile of three voters over three alternatives
has a pairwise-majority cycle `0 ≻ 1 ≻ 2 ≻ 0`. -/
theorem exists_isMajorityCycle :
    ∃ P : Profile (Fin 3) (Fin 3), IsMajorityCycle P 0 1 2 := by
  exact ⟨condorcetProfile, condorcet_cycle⟩

/-- Pairwise majority is not transitive in general. -/
theorem exists_majorityPrefers_not_transitive :
    ∃ P : Profile (Fin 3) (Fin 3),
      MajorityPrefers P 0 1 ∧ MajorityPrefers P 1 2 ∧ ¬ MajorityPrefers P 0 2 := by
  exact ⟨condorcetProfile, condorcet_maj01, condorcet_maj12, condorcet_nmaj02⟩

/-- Some profile has no Condorcet winner: every alternative is beaten by
pairwise majority. -/
theorem exists_no_condorcetWinner :
    ∃ P : Profile (Fin 3) (Fin 3), ∀ a, ∃ b, MajorityPrefers P b a := by
  refine ⟨condorcetProfile, ?_⟩
  intro a
  fin_cases a
  · exact ⟨2, condorcet_maj20⟩
  · exact ⟨0, condorcet_maj01⟩
  · exact ⟨1, condorcet_maj12⟩

end MathlibExt.GameTheory.SocialChoice.CondorcetCycle
