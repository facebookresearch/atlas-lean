/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.SocialChoice.ElectionControl
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-! Examples and checks for `MathlibExt.GameTheory.SocialChoice.ElectionControl`. -/

set_option autoImplicit false

@[expose] public section

namespace MathlibExtTest.GameTheory.SocialChoice.ElectionControl

open Classical
open MathlibExt.GameTheory.SocialChoice
open MathlibExt.GameTheory.SocialChoice.ArrowWanted
open scoped BigOperators

/-- Rank of alternative `a` in voter `i`'s cyclic ranking: voter `i` ranks
`i` first, then `i + 1`, then `i + 2` (mod 3). -/
def cycleRank (i a : Fin 3) : ℕ := (a.val + 3 - i.val) % 3

/-- Each voter's cyclic rank is injective (checked by `decide`). -/
theorem cycleRank_injective_all :
    ∀ (i a b : Fin 3), cycleRank i a = cycleRank i b → a = b := by
  decide

theorem cycleRank_injective (i : Fin 3) : Function.Injective (cycleRank i) :=
  fun _ _ h => cycleRank_injective_all i _ _ h

/-- Voter `i`'s strict preference in the 3-cycle profile. -/
def cycleOrder (i : Fin 3) : StrictTotalOrder (Fin 3) where
  lt := fun a b => cycleRank i a < cycleRank i b
  irrefl := fun a => Nat.lt_irrefl _
  trans := fun h1 h2 => Nat.lt_trans h1 h2
  total := fun {a b} hne => by
    have hRne : cycleRank i a ≠ cycleRank i b :=
      fun h => hne (cycleRank_injective i h)
    exact lt_or_gt_of_ne hRne

/-- The 3-cycle profile: voter `i` ranks `i ≻ i + 1 ≻ i + 2` (mod 3). -/
def cycleP : Profile (Fin 3) (Fin 3) := fun i => cycleOrder i

theorem cycleP_sup01 :
    Finset.univ.filter (fun i : Fin 3 => (cycleP i).lt 0 1) = {0, 2} := by
  have hlt : ∀ (i a b : Fin 3),
      (cycleP i).lt a b ↔ cycleRank i a < cycleRank i b :=
    fun _ _ _ => Iff.rfl
  simp only [hlt]
  decide

theorem cycleP_sup10 :
    Finset.univ.filter (fun i : Fin 3 => (cycleP i).lt 1 0) = {1} := by
  have hlt : ∀ (i a b : Fin 3),
      (cycleP i).lt a b ↔ cycleRank i a < cycleRank i b :=
    fun _ _ _ => Iff.rfl
  simp only [hlt]
  decide

theorem cycleP_sup12 :
    Finset.univ.filter (fun i : Fin 3 => (cycleP i).lt 1 2) = {0, 1} := by
  have hlt : ∀ (i a b : Fin 3),
      (cycleP i).lt a b ↔ cycleRank i a < cycleRank i b :=
    fun _ _ _ => Iff.rfl
  simp only [hlt]
  decide

theorem cycleP_sup21 :
    Finset.univ.filter (fun i : Fin 3 => (cycleP i).lt 2 1) = {2} := by
  have hlt : ∀ (i a b : Fin 3),
      (cycleP i).lt a b ↔ cycleRank i a < cycleRank i b :=
    fun _ _ _ => Iff.rfl
  simp only [hlt]
  decide

theorem cycleP_sup20 :
    Finset.univ.filter (fun i : Fin 3 => (cycleP i).lt 2 0) = {1, 2} := by
  have hlt : ∀ (i a b : Fin 3),
      (cycleP i).lt a b ↔ cycleRank i a < cycleRank i b :=
    fun _ _ _ => Iff.rfl
  simp only [hlt]
  decide

theorem cycleP_sup02 :
    Finset.univ.filter (fun i : Fin 3 => (cycleP i).lt 0 2) = {0} := by
  have hlt : ∀ (i a b : Fin 3),
      (cycleP i).lt a b ↔ cycleRank i a < cycleRank i b :=
    fun _ _ _ => Iff.rfl
  simp only [hlt]
  decide

theorem cycleP_margin01 : netPreference cycleP 0 1 = 1 := by
  unfold netPreference
  rw [cycleP_sup01, cycleP_sup10]
  decide

theorem cycleP_margin12 : netPreference cycleP 1 2 = 1 := by
  unfold netPreference
  rw [cycleP_sup12, cycleP_sup21]
  decide

theorem cycleP_margin20 : netPreference cycleP 2 0 = 1 := by
  unfold netPreference
  rw [cycleP_sup20, cycleP_sup02]
  decide

theorem cycleP_margin02 : netPreference cycleP 0 2 = -1 := by
  unfold netPreference
  rw [cycleP_sup02, cycleP_sup20]
  decide

/-- T1: the 3-cycle margins, and the failure of `0` to be a Condorcet winner. -/
theorem t1_cycle_margins :
    netPreference cycleP 0 1 = 1 ∧
      netPreference cycleP 1 2 = 1 ∧
        netPreference cycleP 2 0 = 1 ∧ ¬ IsCondorcetWinner cycleP 0 := by
  refine ⟨cycleP_margin01, cycleP_margin12, cycleP_margin20, ?_⟩
  intro h
  have h2 := h 2 (by decide : (2 : Fin 3) ≠ 0)
  rw [majorityPrefers_iff_netPreference_pos] at h2
  rw [cycleP_margin02] at h2
  exact absurd h2 (by decide)

/-- Every member of the subtype over `{0, 1}` is `0` or `1`. -/
theorem subtype01_cases (b : {x : Fin 3 // x ∈ ({0, 1} : Finset (Fin 3))}) :
    b = ⟨0, by decide⟩ ∨ b = ⟨1, by decide⟩ := by
  obtain ⟨v, hv⟩ := b
  fin_cases v
  · exact Or.inl (Subtype.ext rfl)
  · exact Or.inr (Subtype.ext rfl)
  · exact absurd hv (by decide)

/-- T2: deleting candidate `2` makes `0` the Condorcet winner. -/
theorem t2_cycle_deleted :
    IsCondorcetWinner (restrictProfile cycleP {0, 1}) ⟨0, by decide⟩ := by
  intro b hb
  obtain ⟨v, hv⟩ := b
  fin_cases v
  · exact (hb (Subtype.ext rfl)).elim
  · rw [majorityPrefers_iff_netPreference_pos]
    rw [netPreference_restrictProfile]
    show (0 : ℤ) < netPreference cycleP 0 1
    rw [cycleP_margin01]
    decide
  · exact absurd hv (by decide)

/-- Rank function for the ballot `2 ≻ 1 ≻ 0`. -/
def rank210 (a : Fin 3) : ℕ := if a = 2 then 0 else if a = 1 then 1 else 2

theorem rank210_injective : Function.Injective rank210 := by decide

/-- Rank function for the ballot `1 ≻ 0 ≻ 2`. -/
def rank102 (a : Fin 3) : ℕ := if a = 1 then 0 else if a = 0 then 1 else 2

theorem rank102_injective : Function.Injective rank102 := by decide

/-- Rank function for the ballot `0 ≻ 2 ≻ 1`. -/
def rank021 (a : Fin 3) : ℕ := if a = 0 then 0 else if a = 2 then 1 else 2

theorem rank021_injective : Function.Injective rank021 := by decide

/-- Voter `i`'s rank function: voters 0-2 rank `2 ≻ 1 ≻ 0`, voters 3-4
rank `1 ≻ 0 ≻ 2`, voters 5-8 rank `0 ≻ 2 ≻ 1`. -/
def plurRank (i : Fin 9) (a : Fin 3) : ℕ :=
  if i < 3 then rank210 a else if i < 5 then rank102 a else rank021 a

theorem plurRank_injective (i : Fin 9) : Function.Injective (plurRank i) := by
  intro a b h
  by_cases h1 : i < 3
  · simp only [plurRank, h1] at h
    exact rank210_injective h
  · by_cases h2 : i < 5
    · simp only [plurRank, h1, h2] at h
      exact rank102_injective h
    · simp only [plurRank, h1, h2] at h
      exact rank021_injective h

/-- Voter `i`'s strict preference in the plurality-spoiler profile. -/
def plurOrder (i : Fin 9) : StrictTotalOrder (Fin 3) where
  lt := fun a b => plurRank i a < plurRank i b
  irrefl := fun a => Nat.lt_irrefl _
  trans := fun h1 h2 => Nat.lt_trans h1 h2
  total := fun {a b} hne => by
    have hRne : plurRank i a ≠ plurRank i b :=
      fun h => hne (plurRank_injective i h)
    exact lt_or_gt_of_ne hRne

/-- The 9-voter plurality-spoiler profile. -/
def plurP : Profile (Fin 3) (Fin 9) := fun i => plurOrder i

/-- Plurality score: one point per voter ranking `a` first. -/
noncomputable def pluralityScore {Alt Voter : Type*} [Fintype Alt]
    [Fintype Voter] [DecidableEq Alt] (P : Profile Alt Voter) (a : Alt) :
    ℤ :=
  scoringScore (fun k => if k = 0 then 1 else 0) P a

theorem rankAbove_plurP_g0_0 {i : Fin 9} (h : i < 3) :
    rankAbove (plurP i) 0 = 2 := by
  have hset : Finset.univ.filter (fun b : Fin 3 => (plurP i).lt b 0) = {1, 2} := by
    have hlt : ∀ (a b : Fin 3),
        (plurP i).lt a b ↔ plurRank i a < plurRank i b :=
      fun _ _ => Iff.rfl
    simp only [hlt, plurRank, h, ite_true, rank210]
    decide
  unfold rankAbove
  rw [hset]
  decide

theorem rankAbove_plurP_g0_1 {i : Fin 9} (h : i < 3) :
    rankAbove (plurP i) 1 = 1 := by
  have hset : Finset.univ.filter (fun b : Fin 3 => (plurP i).lt b 1) = {2} := by
    have hlt : ∀ (a b : Fin 3),
        (plurP i).lt a b ↔ plurRank i a < plurRank i b :=
      fun _ _ => Iff.rfl
    simp only [hlt, plurRank, h, ite_true, rank210]
    decide
  unfold rankAbove
  rw [hset]
  decide

theorem rankAbove_plurP_g0_2 {i : Fin 9} (h : i < 3) :
    rankAbove (plurP i) 2 = 0 := by
  have hset : Finset.univ.filter (fun b : Fin 3 => (plurP i).lt b 2) = ∅ := by
    have hlt : ∀ (a b : Fin 3),
        (plurP i).lt a b ↔ plurRank i a < plurRank i b :=
      fun _ _ => Iff.rfl
    simp only [hlt, plurRank, h, ite_true, rank210]
    decide
  unfold rankAbove
  rw [hset]
  decide

theorem rankAbove_plurP_g1_0 {i : Fin 9} (h1 : ¬ i < 3) (h2 : i < 5) :
    rankAbove (plurP i) 0 = 1 := by
  have hset : Finset.univ.filter (fun b : Fin 3 => (plurP i).lt b 0) = {1} := by
    have hlt : ∀ (a b : Fin 3),
        (plurP i).lt a b ↔ plurRank i a < plurRank i b :=
      fun _ _ => Iff.rfl
    simp only [hlt, plurRank, h1, ite_false, h2, ite_true, rank102]
    decide
  unfold rankAbove
  rw [hset]
  decide

theorem rankAbove_plurP_g1_1 {i : Fin 9} (h1 : ¬ i < 3) (h2 : i < 5) :
    rankAbove (plurP i) 1 = 0 := by
  have hset : Finset.univ.filter (fun b : Fin 3 => (plurP i).lt b 1) = ∅ := by
    have hlt : ∀ (a b : Fin 3),
        (plurP i).lt a b ↔ plurRank i a < plurRank i b :=
      fun _ _ => Iff.rfl
    simp only [hlt, plurRank, h1, ite_false, h2, ite_true, rank102]
    decide
  unfold rankAbove
  rw [hset]
  decide

theorem rankAbove_plurP_g1_2 {i : Fin 9} (h1 : ¬ i < 3) (h2 : i < 5) :
    rankAbove (plurP i) 2 = 2 := by
  have hset : Finset.univ.filter (fun b : Fin 3 => (plurP i).lt b 2) = {0, 1} := by
    have hlt : ∀ (a b : Fin 3),
        (plurP i).lt a b ↔ plurRank i a < plurRank i b :=
      fun _ _ => Iff.rfl
    simp only [hlt, plurRank, h1, ite_false, h2, ite_true, rank102]
    decide
  unfold rankAbove
  rw [hset]
  decide

theorem rankAbove_plurP_g2_0 {i : Fin 9} (h1 : ¬ i < 3) (h2 : ¬ i < 5) :
    rankAbove (plurP i) 0 = 0 := by
  have hset : Finset.univ.filter (fun b : Fin 3 => (plurP i).lt b 0) = ∅ := by
    have hlt : ∀ (a b : Fin 3),
        (plurP i).lt a b ↔ plurRank i a < plurRank i b :=
      fun _ _ => Iff.rfl
    simp only [hlt, plurRank, h1, ite_false, h2, ite_false, rank021]
    decide
  unfold rankAbove
  rw [hset]
  decide

theorem rankAbove_plurP_g2_1 {i : Fin 9} (h1 : ¬ i < 3) (h2 : ¬ i < 5) :
    rankAbove (plurP i) 1 = 2 := by
  have hset : Finset.univ.filter (fun b : Fin 3 => (plurP i).lt b 1) = {0, 2} := by
    have hlt : ∀ (a b : Fin 3),
        (plurP i).lt a b ↔ plurRank i a < plurRank i b :=
      fun _ _ => Iff.rfl
    simp only [hlt, plurRank, h1, ite_false, h2, ite_false, rank021]
    decide
  unfold rankAbove
  rw [hset]
  decide

theorem rankAbove_plurP_g2_2 {i : Fin 9} (h1 : ¬ i < 3) (h2 : ¬ i < 5) :
    rankAbove (plurP i) 2 = 1 := by
  have hset : Finset.univ.filter (fun b : Fin 3 => (plurP i).lt b 2) = {0} := by
    have hlt : ∀ (a b : Fin 3),
        (plurP i).lt a b ↔ plurRank i a < plurRank i b :=
      fun _ _ => Iff.rfl
    simp only [hlt, plurRank, h1, ite_false, h2, ite_false, rank021]
    decide
  unfold rankAbove
  rw [hset]
  decide

theorem voters_plur_0 :
    Finset.univ.filter (fun i : Fin 9 => rankAbove (plurP i) 0 = 0)
      = {5, 6, 7, 8} := by
  ext i
  fin_cases i <;> simp [rankAbove_plurP_g0_0, rankAbove_plurP_g1_0,
    rankAbove_plurP_g2_0, Finset.mem_filter]

theorem voters_plur_1 :
    Finset.univ.filter (fun i : Fin 9 => rankAbove (plurP i) 1 = 0)
      = {3, 4} := by
  ext i
  fin_cases i <;> simp [rankAbove_plurP_g0_1, rankAbove_plurP_g1_1,
    rankAbove_plurP_g2_1, Finset.mem_filter]

theorem voters_plur_2 :
    Finset.univ.filter (fun i : Fin 9 => rankAbove (plurP i) 2 = 0)
      = {0, 1, 2} := by
  ext i
  fin_cases i <;> simp [rankAbove_plurP_g0_2, rankAbove_plurP_g1_2,
    rankAbove_plurP_g2_2, Finset.mem_filter]

theorem score_plur_0 : pluralityScore plurP 0 = 4 := by
  simp only [pluralityScore, scoringScore]
  rw [show (∑ i : Fin 9, (fun k : ℕ => if k = 0 then (1 : ℤ) else 0)
        (rankAbove (plurP i) 0))
      = ∑ i : Fin 9, (if rankAbove (plurP i) 0 = 0 then (1 : ℤ) else 0) from
    Finset.sum_congr rfl (fun i _ => rfl)]
  rw [← Finset.sum_filter]
  simp
  rw [voters_plur_0]
  decide

theorem score_plur_1 : pluralityScore plurP 1 = 2 := by
  simp only [pluralityScore, scoringScore]
  rw [show (∑ i : Fin 9, (fun k : ℕ => if k = 0 then (1 : ℤ) else 0)
        (rankAbove (plurP i) 1))
      = ∑ i : Fin 9, (if rankAbove (plurP i) 1 = 0 then (1 : ℤ) else 0) from
    Finset.sum_congr rfl (fun i _ => rfl)]
  rw [← Finset.sum_filter]
  simp
  rw [voters_plur_1]
  decide

theorem score_plur_2 : pluralityScore plurP 2 = 3 := by
  simp only [pluralityScore, scoringScore]
  rw [show (∑ i : Fin 9, (fun k : ℕ => if k = 0 then (1 : ℤ) else 0)
        (rankAbove (plurP i) 2))
      = ∑ i : Fin 9, (if rankAbove (plurP i) 2 = 0 then (1 : ℤ) else 0) from
    Finset.sum_congr rfl (fun i _ => rfl)]
  rw [← Finset.sum_filter]
  simp
  rw [voters_plur_2]
  decide

theorem winners_plur_full : winners (pluralityScore plurP) = {0} := by
  ext a
  fin_cases a
  · simp only [winners, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro _
      decide
    · intro _ b
      fin_cases b
      · show pluralityScore plurP 0 ≤ pluralityScore plurP 0
        rw [score_plur_0]
      · show pluralityScore plurP 1 ≤ pluralityScore plurP 0
        rw [score_plur_1, score_plur_0]
        decide
      · show pluralityScore plurP 2 ≤ pluralityScore plurP 0
        rw [score_plur_2, score_plur_0]
        decide
  · simp only [winners, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      have h0 : pluralityScore plurP 0 ≤ pluralityScore plurP 1 := h 0
      rw [score_plur_0, score_plur_1] at h0
      exact absurd h0 (by decide)
    · intro hcon
      exact absurd hcon (by decide)
  · simp only [winners, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      have h0 : pluralityScore plurP 0 ≤ pluralityScore plurP 2 := h 0
      rw [score_plur_0, score_plur_2] at h0
      exact absurd h0 (by decide)
    · intro hcon
      exact absurd hcon (by decide)

theorem rankAbove_rPlurP_g0_e1 {i : Fin 9} (h : i < 3) :
    rankAbove ((restrictProfile plurP {0, 1}) i) ⟨1, by decide⟩ = 0 := by
  have hset : Finset.univ.filter
      (fun b : {x : Fin 3 // x ∈ ({0, 1} : Finset (Fin 3))} =>
        ((restrictProfile plurP {0, 1}) i).lt b ⟨1, by decide⟩) = ∅ := by
    have hltR : ∀ (a b : {x : Fin 3 // x ∈ ({0, 1} : Finset (Fin 3))}),
        ((restrictProfile plurP {0, 1}) i).lt a b ↔ (plurP i).lt a.1 b.1 :=
      fun _ _ => Iff.rfl
    have hltP : ∀ (a b : Fin 3),
        (plurP i).lt a b ↔ plurRank i a < plurRank i b :=
      fun _ _ => Iff.rfl
    simp only [hltR, hltP, plurRank, h, ite_true, rank210]
    decide
  unfold rankAbove
  rw [hset]
  decide

theorem rankAbove_rPlurP_g0_e0 {i : Fin 9} (h : i < 3) :
    rankAbove ((restrictProfile plurP {0, 1}) i) ⟨0, by decide⟩ = 1 := by
  have hset : Finset.univ.filter
      (fun b : {x : Fin 3 // x ∈ ({0, 1} : Finset (Fin 3))} =>
        ((restrictProfile plurP {0, 1}) i).lt b ⟨0, by decide⟩)
      = {⟨1, by decide⟩} := by
    have hltR : ∀ (a b : {x : Fin 3 // x ∈ ({0, 1} : Finset (Fin 3))}),
        ((restrictProfile plurP {0, 1}) i).lt a b ↔ (plurP i).lt a.1 b.1 :=
      fun _ _ => Iff.rfl
    have hltP : ∀ (a b : Fin 3),
        (plurP i).lt a b ↔ plurRank i a < plurRank i b :=
      fun _ _ => Iff.rfl
    simp only [hltR, hltP, plurRank, h, ite_true, rank210]
    decide
  unfold rankAbove
  rw [hset]
  decide

theorem rankAbove_rPlurP_g1_e1 {i : Fin 9} (h1 : ¬ i < 3) (h2 : i < 5) :
    rankAbove ((restrictProfile plurP {0, 1}) i) ⟨1, by decide⟩ = 0 := by
  have hset : Finset.univ.filter
      (fun b : {x : Fin 3 // x ∈ ({0, 1} : Finset (Fin 3))} =>
        ((restrictProfile plurP {0, 1}) i).lt b ⟨1, by decide⟩) = ∅ := by
    have hltR : ∀ (a b : {x : Fin 3 // x ∈ ({0, 1} : Finset (Fin 3))}),
        ((restrictProfile plurP {0, 1}) i).lt a b ↔ (plurP i).lt a.1 b.1 :=
      fun _ _ => Iff.rfl
    have hltP : ∀ (a b : Fin 3),
        (plurP i).lt a b ↔ plurRank i a < plurRank i b :=
      fun _ _ => Iff.rfl
    simp only [hltR, hltP, plurRank, h1, ite_false, h2, ite_true, rank102]
    decide
  unfold rankAbove
  rw [hset]
  decide

theorem rankAbove_rPlurP_g1_e0 {i : Fin 9} (h1 : ¬ i < 3) (h2 : i < 5) :
    rankAbove ((restrictProfile plurP {0, 1}) i) ⟨0, by decide⟩ = 1 := by
  have hset : Finset.univ.filter
      (fun b : {x : Fin 3 // x ∈ ({0, 1} : Finset (Fin 3))} =>
        ((restrictProfile plurP {0, 1}) i).lt b ⟨0, by decide⟩)
      = {⟨1, by decide⟩} := by
    have hltR : ∀ (a b : {x : Fin 3 // x ∈ ({0, 1} : Finset (Fin 3))}),
        ((restrictProfile plurP {0, 1}) i).lt a b ↔ (plurP i).lt a.1 b.1 :=
      fun _ _ => Iff.rfl
    have hltP : ∀ (a b : Fin 3),
        (plurP i).lt a b ↔ plurRank i a < plurRank i b :=
      fun _ _ => Iff.rfl
    simp only [hltR, hltP, plurRank, h1, ite_false, h2, ite_true, rank102]
    decide
  unfold rankAbove
  rw [hset]
  decide

theorem rankAbove_rPlurP_g2_e1 {i : Fin 9} (h1 : ¬ i < 3) (h2 : ¬ i < 5) :
    rankAbove ((restrictProfile plurP {0, 1}) i) ⟨1, by decide⟩ = 1 := by
  have hset : Finset.univ.filter
      (fun b : {x : Fin 3 // x ∈ ({0, 1} : Finset (Fin 3))} =>
        ((restrictProfile plurP {0, 1}) i).lt b ⟨1, by decide⟩)
      = {⟨0, by decide⟩} := by
    have hltR : ∀ (a b : {x : Fin 3 // x ∈ ({0, 1} : Finset (Fin 3))}),
        ((restrictProfile plurP {0, 1}) i).lt a b ↔ (plurP i).lt a.1 b.1 :=
      fun _ _ => Iff.rfl
    have hltP : ∀ (a b : Fin 3),
        (plurP i).lt a b ↔ plurRank i a < plurRank i b :=
      fun _ _ => Iff.rfl
    simp only [hltR, hltP, plurRank, h1, ite_false, h2, ite_false, rank021]
    decide
  unfold rankAbove
  rw [hset]
  decide

theorem rankAbove_rPlurP_g2_e0 {i : Fin 9} (h1 : ¬ i < 3) (h2 : ¬ i < 5) :
    rankAbove ((restrictProfile plurP {0, 1}) i) ⟨0, by decide⟩ = 0 := by
  have hset : Finset.univ.filter
      (fun b : {x : Fin 3 // x ∈ ({0, 1} : Finset (Fin 3))} =>
        ((restrictProfile plurP {0, 1}) i).lt b ⟨0, by decide⟩) = ∅ := by
    have hltR : ∀ (a b : {x : Fin 3 // x ∈ ({0, 1} : Finset (Fin 3))}),
        ((restrictProfile plurP {0, 1}) i).lt a b ↔ (plurP i).lt a.1 b.1 :=
      fun _ _ => Iff.rfl
    have hltP : ∀ (a b : Fin 3),
        (plurP i).lt a b ↔ plurRank i a < plurRank i b :=
      fun _ _ => Iff.rfl
    simp only [hltR, hltP, plurRank, h1, ite_false, h2, ite_false, rank021]
    decide
  unfold rankAbove
  rw [hset]
  decide

theorem voters_rPlur_e1 :
    Finset.univ.filter
      (fun i : Fin 9 =>
        rankAbove ((restrictProfile plurP {0, 1}) i) ⟨1, by decide⟩ = 0)
      = {0, 1, 2, 3, 4} := by
  ext i
  fin_cases i <;> simp [rankAbove_rPlurP_g0_e1, rankAbove_rPlurP_g1_e1,
    rankAbove_rPlurP_g2_e1, Finset.mem_filter]

theorem voters_rPlur_e0 :
    Finset.univ.filter
      (fun i : Fin 9 =>
        rankAbove ((restrictProfile plurP {0, 1}) i) ⟨0, by decide⟩ = 0)
      = {5, 6, 7, 8} := by
  ext i
  fin_cases i <;> simp [rankAbove_rPlurP_g0_e0, rankAbove_rPlurP_g1_e0,
    rankAbove_rPlurP_g2_e0, Finset.mem_filter]

theorem score_rPlur_e1 :
    pluralityScore (restrictProfile plurP {0, 1}) ⟨1, by decide⟩ = 5 := by
  simp only [pluralityScore, scoringScore]
  rw [show (∑ i : Fin 9, (fun k : ℕ => if k = 0 then (1 : ℤ) else 0)
        (rankAbove ((restrictProfile plurP {0, 1}) i) ⟨1, by decide⟩))
      = ∑ i : Fin 9, (if rankAbove ((restrictProfile plurP {0, 1}) i)
        ⟨1, by decide⟩ = 0 then (1 : ℤ) else 0) from
    Finset.sum_congr rfl (fun i _ => rfl)]
  rw [← Finset.sum_filter]
  simp
  rw [voters_rPlur_e1]
  decide

theorem score_rPlur_e0 :
    pluralityScore (restrictProfile plurP {0, 1}) ⟨0, by decide⟩ = 4 := by
  simp only [pluralityScore, scoringScore]
  rw [show (∑ i : Fin 9, (fun k : ℕ => if k = 0 then (1 : ℤ) else 0)
        (rankAbove ((restrictProfile plurP {0, 1}) i) ⟨0, by decide⟩))
      = ∑ i : Fin 9, (if rankAbove ((restrictProfile plurP {0, 1}) i)
        ⟨0, by decide⟩ = 0 then (1 : ℤ) else 0) from
    Finset.sum_congr rfl (fun i _ => rfl)]
  rw [← Finset.sum_filter]
  simp
  rw [voters_rPlur_e0]
  decide

/-- T3: the plurality spoiler - `0` wins outright with all candidates, but
deleting `2` hands the election to `1`. -/
theorem t3_plurality_spoiler :
    winners (pluralityScore plurP) = {0} ∧
      pluralityScore (restrictProfile plurP {0, 1}) ⟨1, by decide⟩ = 5 ∧
        pluralityScore (restrictProfile plurP {0, 1}) ⟨0, by decide⟩ = 4 :=
  ⟨winners_plur_full, score_rPlur_e1, score_rPlur_e0⟩

/-- A unanimous profile: every voter uses voter `0`'s cyclic order. -/
def unanP : Profile (Fin 3) (Fin 3) := fun _ => cycleOrder 0

theorem unanP_net01 : netPreference unanP 0 1 = 3 := by
  unfold netPreference
  have hf1 : Finset.univ.filter (fun i : Fin 3 => (unanP i).lt 0 1) =
      Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    show cycleRank 0 0 < cycleRank 0 1 ↔ True
    decide
  have hf2 : Finset.univ.filter (fun i : Fin 3 => (unanP i).lt 1 0) = ∅ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty]
    show cycleRank 0 1 < cycleRank 0 0 ↔ False
    decide
  rw [hf1, hf2]
  decide

theorem unanP_net02 : netPreference unanP 0 2 = 3 := by
  unfold netPreference
  have hf1 : Finset.univ.filter (fun i : Fin 3 => (unanP i).lt 0 2) =
      Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    show cycleRank 0 0 < cycleRank 0 2 ↔ True
    decide
  have hf2 : Finset.univ.filter (fun i : Fin 3 => (unanP i).lt 2 0) = ∅ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty]
    show cycleRank 0 2 < cycleRank 0 0 ↔ False
    decide
  rw [hf1, hf2]
  decide

theorem unanP_winner : IsCondorcetWinner unanP 0 := by
  intro b hb
  fin_cases b
  · exact absurd rfl hb
  · rw [majorityPrefers_iff_netPreference_pos]
    show (0 : ℤ) < netPreference unanP 0 1
    rw [unanP_net01]; decide
  · rw [majorityPrefers_iff_netPreference_pos]
    show (0 : ℤ) < netPreference unanP 0 2
    rw [unanP_net02]; decide

/-- T4: the immunity theorem, applied to the cycle at every budget. -/
theorem t4_no_adding_control_cycle (k : ℕ) :
    ¬ CanControlByAddingCandidates cycleP {0, 1} 0 k :=
  not_canControlByAddingCandidates cycleP {0, 1} 0 k

/-- T5: the deleting-candidates susceptibility existential. -/
theorem t5_exists_deleting_control :
    ∃ (P : Profile (Fin 3) (Fin 3)) (p : Fin 3) (S : Finset (Fin 3))
      (hp : p ∈ S),
      ¬ IsCondorcetWinner P p ∧
        IsCondorcetWinner (restrictProfile P S) ⟨p, hp⟩ ∧ S.card = 2 :=
  exists_controlByDeletingCandidates

/-- T6: restriction preserves the unanimous Condorcet winner. -/
theorem t6_restricted_unan_winner :
    IsCondorcetWinner (restrictProfile unanP {0, 2}) ⟨0, by decide⟩ :=
  isCondorcetWinner_restrictProfile unanP {0, 2} (by decide) unanP_winner

end MathlibExtTest.GameTheory.SocialChoice.ElectionControl
end
