/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.Unbundled
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import MathlibExt.Order.StrictTotalOrder
public import MathlibExt.GameTheory.SocialChoice.Arrow
public import MathlibExt.GameTheory.SocialChoice.CondorcetCycle
import MathlibExt.GameTheory.Matching.StableMechanism
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Single-peakedness and Borda

This module audits part of the core social-choice interface: Black's
single-peakedness transitivity result and the Borda count with its
independence-of-irrelevant-alternatives failure. The Arrow bridge audit
lives in the test module `MathlibExtTest.GameTheory.SocialChoice.Black`.

## Canonical interface

The five existing developments below form the canonical social-choice
interface. The `ArrowWanted` development is the canonical Arrow statement
going forward.

- `MathlibExt.GameTheory.SocialChoice.ArrowWanted`: Arrow's theorem for social
  welfare functions on strict total orders (`arrow_impossibility` and
  `arrow_impossibility_general`).
- `MetaMathlibExt.arrowImpossibility` (`ArrowImpossibility`): Arrow's theorem
  for rules on preorder-valued profiles over a `Finset` electorate.
- `MathlibExt.GameTheory.SocialChoice.CondorcetCycle`: pairwise majority
  (`supporters`, `MajorityPrefers`, `IsMajorityCycle`).
- `GibbardSatterthwaiteWanted.gibbard_satterthwaite` (record only).
- `SinglePeakedProfile.isCondorcetWinner_of_median` (record only).

## Clause map

- C1, Arrow bridge from the relation form to the strict form: audited in
  the test module `MathlibExtTest.GameTheory.SocialChoice.Black`.
- C2, converse bridge (strict form implies relation form): omitted, since
  indifference obstructs the transfer (a linearization breaks one of the two
  comparisons relation-IIA needs at an indifferent pair); the relation form is
  proved directly in `MathlibExt.GameTheory.SocialChoice.ArrowImpossibility`.
- C3, ordinal single-peakedness: `IsSinglePeaked`, `top_of_isSinglePeaked`.
- C4, Black's transitivity: `majorityPrefers_trans_of_singlePeaked`, with
  helpers `supporters_eq_filter`, `mem_supporters`, `majorityPrefers_iff`,
  `strict_asymm`, `not_majority_both`, `majorityPrefers_of_not`,
  `not_below_both_of_singlePeaked`, `supporters_zy_subset_zx`,
  `supporters_xy_subset_xz`, `no_cycle_forward`, `no_cycle_backward`.
- C5, Borda score: `bordaScore`, `bordaScore_unfold`.
- C6, Borda violates IIA: `borda_score_reversal`, with public helper
  `rankOrder`; the concrete ballots, profiles, and computation lemmas
  are private witness scaffolding.

Reverse map: every public declaration's docstring names its clause.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.GameTheory.SocialChoice

open MathlibExt.Order
open MathlibExt.GameTheory.SocialChoice.ArrowWanted
open MathlibExt.GameTheory.SocialChoice.CondorcetCycle
open MathlibExt.GameTheory.Matching.StableMechanism

/-
C2 note: the converse bridge (strict form implies relation form) is not
included here. Voter indifference obstructs the transfer: a linearization
breaks one of the two comparisons that relation-form IIA needs at an
indifferent pair. The relation form itself is proved directly in
`MathlibExt.GameTheory.SocialChoice.ArrowImpossibility`.
-/

/-- Ordinal single-peakedness (C3): every voter has a peak alternative, with
strict preference increasing towards the peak from the left and decreasing
away from the peak to the right. -/
def IsSinglePeaked {Alt Voter : Type*} [LinearOrder Alt] (P : Profile Alt Voter) :
    Prop :=
  ∀ i : Voter, ∃ p : Alt,
    (∀ a b : Alt, a < b → b ≤ p → (P i).lt b a) ∧
      ∀ a b : Alt, p ≤ a → a < b → (P i).lt a b

/-- Characterization (C3): a single-peaked voter's peak is their top
alternative, strictly preferred to every other alternative. -/
theorem top_of_isSinglePeaked {Alt Voter : Type*} [LinearOrder Alt]
    {P : Profile Alt Voter} (hP : IsSinglePeaked P) (i : Voter) :
    ∃ p : Alt, ∀ x : Alt, x ≠ p → (P i).lt p x := by
  obtain ⟨p, hleft, hright⟩ := hP i
  refine ⟨p, fun x hx => ?_⟩
  rcases lt_or_gt_of_ne hx with h | h
  · exact hleft x p h le_rfl
  · exact hright p x le_rfl h

open Classical in
/-- `supporters` as a filter (helper for C4). -/
theorem supporters_eq_filter {Alt Voter : Type*} [Fintype Voter]
    (P : Profile Alt Voter) (a b : Alt) :
    supporters P a b = Finset.univ.filter fun i : Voter => (P i).lt a b :=
  rfl

/-- Membership in `supporters` (helper for C4). -/
theorem mem_supporters {Alt Voter : Type*} [Fintype Voter] (P : Profile Alt Voter)
    (a b : Alt) (i : Voter) : i ∈ supporters P a b ↔ (P i).lt a b := by
  classical
  rw [supporters_eq_filter, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ i, h⟩⟩

/-- Unfolding for `MajorityPrefers` (helper for C4). -/
theorem majorityPrefers_iff {Alt Voter : Type*} [Fintype Voter]
    (P : Profile Alt Voter) (a b : Alt) :
    MajorityPrefers P a b ↔
      Fintype.card Voter < 2 * (supporters P a b).card :=
  Iff.rfl

/-- Individual strict preference is asymmetric (helper for C4). -/
theorem strict_asymm {Alt Voter : Type*} (P : Profile Alt Voter) (i : Voter)
    (a b : Alt) (h1 : (P i).lt a b) (h2 : (P i).lt b a) : False :=
  (P i).irrefl a ((P i).trans h1 h2)

open Classical in
/-- Majority is asymmetric (helper for C4). -/
theorem not_majority_both {Alt Voter : Type*} [Fintype Voter]
    (P : Profile Alt Voter) (a b : Alt) (hab : MajorityPrefers P a b)
    (hba : MajorityPrefers P b a) : False := by
  rw [majorityPrefers_iff] at hab hba
  have hsub : supporters P b a ⊆
      Finset.univ.filter fun i : Voter => ¬ (P i).lt a b := by
    intro i hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ i, fun h => ?_⟩
    exact strict_asymm P i a b h ((mem_supporters P b a i).mp hi)
  have hle := Finset.card_le_card hsub
  have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : Voter => (P i).lt a b)
  rw [Finset.card_univ] at hsum
  rw [supporters_eq_filter] at hab hba
  have hcard := congrArg Finset.card (supporters_eq_filter P b a)
  omega

open Classical in
/-- With an odd electorate, failure of majority flips (helper for C4). -/
theorem majorityPrefers_of_not {Alt Voter : Type*} [Fintype Voter]
    (P : Profile Alt Voter) (hodd : Odd (Fintype.card Voter)) {a c : Alt}
    (hne : a ≠ c) (h : ¬ MajorityPrefers P a c) : MajorityPrefers P c a := by
  rw [majorityPrefers_iff] at h ⊢
  have hsub : Finset.univ.filter (fun i : Voter => ¬ (P i).lt a c) ⊆
      supporters P c a := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [mem_supporters]
    rcases (P i).total hne with hlt | hlt
    · exact absurd hlt hi.2
    · exact hlt
  have hle := Finset.card_le_card hsub
  have hsum := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : Voter => (P i).lt a c)
  rw [Finset.card_univ] at hsum
  rw [supporters_eq_filter] at h hle ⊢
  obtain ⟨k, hk⟩ := hodd
  omega

/-- Value restriction (C4): under single-peakedness, no voter ranks the middle
of three ordered alternatives strictly below both extremes. -/
theorem not_below_both_of_singlePeaked {Alt Voter : Type*} [LinearOrder Alt]
    {P : Profile Alt Voter} (hP : IsSinglePeaked P) {x y z : Alt} (hxy : x < y)
    (hyz : y < z) (i : Voter) : ¬ ((P i).lt x y ∧ (P i).lt z y) := by
  obtain ⟨p, hleft, hright⟩ := hP i
  rintro ⟨h1, h2⟩
  rcases le_total p y with hle | hle
  · exact (P i).irrefl y ((P i).trans (hright y z hle hyz) h2)
  · exact (P i).irrefl x ((P i).trans h1 (hleft x y hxy hle))

/-- Supporter inclusion, upper side (helper for C4): for `x < y < z`, voters
preferring `z` to `y` also prefer `z` to `x`. -/
theorem supporters_zy_subset_zx {Alt Voter : Type*} [LinearOrder Alt]
    [Fintype Voter] {P : Profile Alt Voter} (hP : IsSinglePeaked P)
    {x y z : Alt} (hxy : x < y) (hyz : y < z) :
    supporters P z y ⊆ supporters P z x := by
  intro i hi
  rw [mem_supporters] at hi ⊢
  by_contra hcon
  have hne : x ≠ z := ne_of_lt (lt_trans hxy hyz)
  rcases (P i).total hne with h | h
  · exact not_below_both_of_singlePeaked hP hxy hyz i ⟨(P i).trans h hi, hi⟩
  · exact hcon h

/-- Supporter inclusion, lower side (helper for C4): for `x < y < z`, voters
preferring `x` to `y` also prefer `x` to `z`. -/
theorem supporters_xy_subset_xz {Alt Voter : Type*} [LinearOrder Alt]
    [Fintype Voter] {P : Profile Alt Voter} (hP : IsSinglePeaked P)
    {x y z : Alt} (hxy : x < y) (hyz : y < z) :
    supporters P x y ⊆ supporters P x z := by
  intro i hi
  rw [mem_supporters] at hi ⊢
  by_contra hcon
  have hne : x ≠ z := ne_of_lt (lt_trans hxy hyz)
  rcases (P i).total hne with h | h
  · exact hcon h
  · exact not_below_both_of_singlePeaked hP hxy hyz i ⟨hi, (P i).trans h hi⟩

/-- No forward majority cycle on a sorted triple (helper for C4). -/
theorem no_cycle_forward {Alt Voter : Type*} [LinearOrder Alt] [Fintype Voter]
    {P : Profile Alt Voter} (hP : IsSinglePeaked P) {x y z : Alt} (hxy : x < y)
    (hyz : y < z) (h1 : MajorityPrefers P x y) (_h2 : MajorityPrefers P y z)
    (h3 : MajorityPrefers P z x) : False := by
  have hle := Finset.card_le_card (supporters_xy_subset_xz hP hxy hyz)
  rw [majorityPrefers_iff] at h1
  have hxz : Fintype.card Voter < 2 * (supporters P x z).card := by omega
  exact not_majority_both P x z ((majorityPrefers_iff P x z).mpr hxz) h3

/-- No backward majority cycle on a sorted triple (helper for C4). -/
theorem no_cycle_backward {Alt Voter : Type*} [LinearOrder Alt] [Fintype Voter]
    {P : Profile Alt Voter} (hP : IsSinglePeaked P) {x y z : Alt} (hxy : x < y)
    (hyz : y < z) (h1 : MajorityPrefers P x z) (h2 : MajorityPrefers P z y)
    (_h3 : MajorityPrefers P y x) : False := by
  have hle := Finset.card_le_card (supporters_zy_subset_zx hP hxy hyz)
  rw [majorityPrefers_iff] at h2
  have hzx : Fintype.card Voter < 2 * (supporters P z x).card := by omega
  exact not_majority_both P z x ((majorityPrefers_iff P z x).mpr hzx) h1

/-- Black's transitivity clause (C4): under single-peakedness with an odd
electorate, the pairwise-majority relation is transitive. -/
theorem majorityPrefers_trans_of_singlePeaked {Alt Voter : Type*} [LinearOrder Alt]
    [Fintype Voter] (P : Profile Alt Voter) (hP : IsSinglePeaked P)
    (hodd : Odd (Fintype.card Voter)) {a b c : Alt} (hab : MajorityPrefers P a b)
    (hbc : MajorityPrefers P b c) : MajorityPrefers P a c := by
  by_cases hab_eq : a = b
  · subst hab_eq
    exact hbc
  by_cases hbc_eq : b = c
  · subst hbc_eq
    exact hab
  by_cases hac_eq : a = c
  · subst hac_eq
    exact False.elim (not_majority_both P _ _ hab hbc)
  by_contra hcon
  have hca : MajorityPrefers P c a := majorityPrefers_of_not P hodd hac_eq hcon
  rcases lt_trichotomy a b with hlt | heq | hgt
  · rcases lt_trichotomy b c with hlt2 | heq2 | hgt2
    · exact no_cycle_forward hP hlt hlt2 hab hbc hca
    · exact absurd heq2 hbc_eq
    · rcases lt_trichotomy a c with hlt3 | heq3 | hgt3
      · exact no_cycle_backward hP hlt3 hgt2 hab hbc hca
      · exact absurd heq3 hac_eq
      · exact no_cycle_forward hP hgt3 hlt hca hab hbc
  · exact absurd heq hab_eq
  · rcases lt_trichotomy b c with hlt2 | heq2 | hgt2
    · rcases lt_trichotomy a c with hlt3 | heq3 | hgt3
      · exact no_cycle_backward hP hgt hlt3 hbc hca hab
      · exact absurd heq3 hac_eq
      · exact no_cycle_forward hP hlt2 hgt3 hbc hca hab
    · exact absurd heq2 hbc_eq
    · exact no_cycle_backward hP hgt2 hgt hca hab hbc

open Classical in
/-- Borda score (C5): for each voter, count the alternatives ranked strictly
below `a`, then sum over voters. -/
noncomputable def bordaScore {Alt Voter : Type*} [Fintype Alt] [Fintype Voter]
    (P : Profile Alt Voter) (a : Alt) : Nat :=
  ∑ i : Voter, (Finset.univ.filter fun b : Alt => (P i).lt a b).card

open Classical in
/-- Unfolding lemma for `bordaScore` (C5). -/
theorem bordaScore_unfold {Alt Voter : Type*} [Fintype Alt] [Fintype Voter]
    (P : Profile Alt Voter) (a : Alt) :
    bordaScore P a =
      ∑ i : Voter, (Finset.univ.filter fun b : Alt => (P i).lt a b).card :=
  rfl

/-- Ballot ranking `0 > 1 > 2`, best first (helper for C6). -/
private def ballot012 : ArrowWanted.StrictTotalOrder (Fin 3) := rankOrder ![0, 1, 2] (by decide)

/-- Ballot ranking `1 > 0 > 2`, best first (helper for C6). -/
private def ballot102 : ArrowWanted.StrictTotalOrder (Fin 3) := rankOrder ![1, 0, 2] (by decide)

/-- Ballot ranking `1 > 2 > 0`, best first (helper for C6). -/
private def ballot120 : ArrowWanted.StrictTotalOrder (Fin 3) := rankOrder ![2, 0, 1] (by decide)

/-- Unfolding for `ballot012` (helper for C6). -/
private theorem ballot012_lt (a b : Fin 3) :
    ballot012.lt a b ↔ ![0, 1, 2] a < ![0, 1, 2] b :=
  Iff.rfl

/-- Unfolding for `ballot102` (helper for C6). -/
private theorem ballot102_lt (a b : Fin 3) :
    ballot102.lt a b ↔ ![1, 0, 2] a < ![1, 0, 2] b :=
  Iff.rfl

/-- Unfolding for `ballot120` (helper for C6). -/
private theorem ballot120_lt (a b : Fin 3) :
    ballot120.lt a b ↔ ![2, 0, 1] a < ![2, 0, 1] b :=
  Iff.rfl

/-- First Borda profile (C6): voters `0 1 2` rank `0 > 1 > 2` and voters `3 4`
rank `1 > 0 > 2`, best first. -/
private def bordaP : Profile (Fin 3) (Fin 5) :=
  ![ballot012, ballot012, ballot012, ballot102, ballot102]

/-- Second Borda profile (C6): voters `0 1 2` rank `0 > 1 > 2` and voters `3 4`
rank `1 > 2 > 0`, best first. -/
private def bordaQ : Profile (Fin 3) (Fin 5) :=
  ![ballot012, ballot012, ballot012, ballot120, ballot120]

/-- Application fact for `bordaP` (helper for C6). -/
private theorem bordaP_zero : bordaP 0 = ballot012 := rfl

/-- Application fact for `bordaP` (helper for C6). -/
private theorem bordaP_one : bordaP 1 = ballot012 := rfl

/-- Application fact for `bordaP` (helper for C6). -/
private theorem bordaP_two : bordaP 2 = ballot012 := rfl

/-- Application fact for `bordaP` (helper for C6). -/
private theorem bordaP_three : bordaP 3 = ballot102 := rfl

/-- Application fact for `bordaP` (helper for C6). -/
private theorem bordaP_four : bordaP 4 = ballot102 := rfl

/-- Application fact for `bordaQ` (helper for C6). -/
private theorem bordaQ_zero : bordaQ 0 = ballot012 := rfl

/-- Application fact for `bordaQ` (helper for C6). -/
private theorem bordaQ_one : bordaQ 1 = ballot012 := rfl

/-- Application fact for `bordaQ` (helper for C6). -/
private theorem bordaQ_two : bordaQ 2 = ballot012 := rfl

/-- Application fact for `bordaQ` (helper for C6). -/
private theorem bordaQ_three : bordaQ 3 = ballot120 := rfl

/-- Application fact for `bordaQ` (helper for C6). -/
private theorem bordaQ_four : bordaQ 4 = ballot120 := rfl

open Classical in
/-- Filter-card fact for `ballot012` (helper for C6). -/
private theorem filterCard_012_0 :
    (Finset.univ.filter fun b : Fin 3 => ballot012.lt 0 b).card = 2 := by
  have h0 : ¬ ballot012.lt 0 0 := by rw [ballot012_lt]; decide
  have h1 : ballot012.lt 0 1 := by rw [ballot012_lt]; decide
  have h2 : ballot012.lt 0 2 := by rw [ballot012_lt]; decide
  rw [Finset.card_filter, Fin.sum_univ_three, ite_eq_right h0, ite_eq_left h1,
    ite_eq_left h2]

open Classical in
/-- Filter-card fact for `ballot012` (helper for C6). -/
private theorem filterCard_012_1 :
    (Finset.univ.filter fun b : Fin 3 => ballot012.lt 1 b).card = 1 := by
  have h0 : ¬ ballot012.lt 1 0 := by rw [ballot012_lt]; decide
  have h1 : ¬ ballot012.lt 1 1 := by rw [ballot012_lt]; decide
  have h2 : ballot012.lt 1 2 := by rw [ballot012_lt]; decide
  rw [Finset.card_filter, Fin.sum_univ_three, ite_eq_right h0, ite_eq_right h1,
    ite_eq_left h2]

open Classical in
/-- Filter-card fact for `ballot012` (helper for C6). -/
private theorem filterCard_012_2 :
    (Finset.univ.filter fun b : Fin 3 => ballot012.lt 2 b).card = 0 := by
  have h0 : ¬ ballot012.lt 2 0 := by rw [ballot012_lt]; decide
  have h1 : ¬ ballot012.lt 2 1 := by rw [ballot012_lt]; decide
  have h2 : ¬ ballot012.lt 2 2 := by rw [ballot012_lt]; decide
  rw [Finset.card_filter, Fin.sum_univ_three, ite_eq_right h0, ite_eq_right h1,
    ite_eq_right h2]

open Classical in
/-- Filter-card fact for `ballot102` (helper for C6). -/
private theorem filterCard_102_0 :
    (Finset.univ.filter fun b : Fin 3 => ballot102.lt 0 b).card = 1 := by
  have h0 : ¬ ballot102.lt 0 0 := by rw [ballot102_lt]; decide
  have h1 : ¬ ballot102.lt 0 1 := by rw [ballot102_lt]; decide
  have h2 : ballot102.lt 0 2 := by rw [ballot102_lt]; decide
  rw [Finset.card_filter, Fin.sum_univ_three, ite_eq_right h0, ite_eq_right h1,
    ite_eq_left h2]

open Classical in
/-- Filter-card fact for `ballot102` (helper for C6). -/
private theorem filterCard_102_1 :
    (Finset.univ.filter fun b : Fin 3 => ballot102.lt 1 b).card = 2 := by
  have h0 : ballot102.lt 1 0 := by rw [ballot102_lt]; decide
  have h1 : ¬ ballot102.lt 1 1 := by rw [ballot102_lt]; decide
  have h2 : ballot102.lt 1 2 := by rw [ballot102_lt]; decide
  rw [Finset.card_filter, Fin.sum_univ_three, ite_eq_left h0, ite_eq_right h1,
    ite_eq_left h2]

open Classical in
/-- Filter-card fact for `ballot102` (helper for C6). -/
private theorem filterCard_102_2 :
    (Finset.univ.filter fun b : Fin 3 => ballot102.lt 2 b).card = 0 := by
  have h0 : ¬ ballot102.lt 2 0 := by rw [ballot102_lt]; decide
  have h1 : ¬ ballot102.lt 2 1 := by rw [ballot102_lt]; decide
  have h2 : ¬ ballot102.lt 2 2 := by rw [ballot102_lt]; decide
  rw [Finset.card_filter, Fin.sum_univ_three, ite_eq_right h0, ite_eq_right h1,
    ite_eq_right h2]

open Classical in
/-- Filter-card fact for `ballot120` (helper for C6). -/
private theorem filterCard_120_0 :
    (Finset.univ.filter fun b : Fin 3 => ballot120.lt 0 b).card = 0 := by
  have h0 : ¬ ballot120.lt 0 0 := by rw [ballot120_lt]; decide
  have h1 : ¬ ballot120.lt 0 1 := by rw [ballot120_lt]; decide
  have h2 : ¬ ballot120.lt 0 2 := by rw [ballot120_lt]; decide
  rw [Finset.card_filter, Fin.sum_univ_three, ite_eq_right h0, ite_eq_right h1,
    ite_eq_right h2]

open Classical in
/-- Filter-card fact for `ballot120` (helper for C6). -/
private theorem filterCard_120_1 :
    (Finset.univ.filter fun b : Fin 3 => ballot120.lt 1 b).card = 2 := by
  have h0 : ballot120.lt 1 0 := by rw [ballot120_lt]; decide
  have h1 : ¬ ballot120.lt 1 1 := by rw [ballot120_lt]; decide
  have h2 : ballot120.lt 1 2 := by rw [ballot120_lt]; decide
  rw [Finset.card_filter, Fin.sum_univ_three, ite_eq_left h0, ite_eq_right h1,
    ite_eq_left h2]

open Classical in
/-- Filter-card fact for `ballot120` (helper for C6). -/
private theorem filterCard_120_2 :
    (Finset.univ.filter fun b : Fin 3 => ballot120.lt 2 b).card = 1 := by
  have h0 : ballot120.lt 2 0 := by rw [ballot120_lt]; decide
  have h1 : ¬ ballot120.lt 2 1 := by rw [ballot120_lt]; decide
  have h2 : ¬ ballot120.lt 2 2 := by rw [ballot120_lt]; decide
  rw [Finset.card_filter, Fin.sum_univ_three, ite_eq_left h0, ite_eq_right h1,
    ite_eq_right h2]

/-- Borda score computation for `bordaP` (helper for C6). -/
private theorem bordaScore_bordaP_zero : bordaScore bordaP 0 = 8 := by
  rw [bordaScore_unfold, Fin.sum_univ_five, bordaP_zero, bordaP_one, bordaP_two,
    bordaP_three, bordaP_four, filterCard_012_0, filterCard_102_0]

/-- Borda score computation for `bordaP` (helper for C6). -/
private theorem bordaScore_bordaP_one : bordaScore bordaP 1 = 7 := by
  rw [bordaScore_unfold, Fin.sum_univ_five, bordaP_zero, bordaP_one, bordaP_two,
    bordaP_three, bordaP_four, filterCard_012_1, filterCard_102_1]

/-- Borda score computation for `bordaP` (helper for C6). -/
private theorem bordaScore_bordaP_two : bordaScore bordaP 2 = 0 := by
  rw [bordaScore_unfold, Fin.sum_univ_five, bordaP_zero, bordaP_one, bordaP_two,
    bordaP_three, bordaP_four, filterCard_012_2, filterCard_102_2]

/-- Borda score computation for `bordaQ` (helper for C6). -/
private theorem bordaScore_bordaQ_zero : bordaScore bordaQ 0 = 6 := by
  rw [bordaScore_unfold, Fin.sum_univ_five, bordaQ_zero, bordaQ_one, bordaQ_two,
    bordaQ_three, bordaQ_four, filterCard_012_0, filterCard_120_0]

/-- Borda score computation for `bordaQ` (helper for C6). -/
private theorem bordaScore_bordaQ_one : bordaScore bordaQ 1 = 7 := by
  rw [bordaScore_unfold, Fin.sum_univ_five, bordaQ_zero, bordaQ_one, bordaQ_two,
    bordaQ_three, bordaQ_four, filterCard_012_1, filterCard_120_1]

/-- Borda score computation for `bordaQ` (helper for C6). -/
private theorem bordaScore_bordaQ_two : bordaScore bordaQ 2 = 2 := by
  rw [bordaScore_unfold, Fin.sum_univ_five, bordaQ_zero, bordaQ_one, bordaQ_two,
    bordaQ_three, bordaQ_four, filterCard_012_2, filterCard_120_2]

/-- Voterwise agreement on `0` vs `1` between the Borda profiles (C6). -/
private theorem borda_agreement :
    ∀ i : Fin 5, (bordaP i).lt 0 1 ↔ (bordaQ i).lt 0 1 := by
  intro i
  fin_cases i
  · change (bordaP 0).lt 0 1 ↔ (bordaQ 0).lt 0 1
    rw [bordaP_zero, bordaQ_zero, ballot012_lt]
  · change (bordaP 1).lt 0 1 ↔ (bordaQ 1).lt 0 1
    rw [bordaP_one, bordaQ_one, ballot012_lt]
  · change (bordaP 2).lt 0 1 ↔ (bordaQ 2).lt 0 1
    rw [bordaP_two, bordaQ_two, ballot012_lt]
  · change (bordaP 3).lt 0 1 ↔ (bordaQ 3).lt 0 1
    rw [bordaP_three, bordaQ_three, ballot102_lt, ballot120_lt]
    decide
  · change (bordaP 4).lt 0 1 ↔ (bordaQ 4).lt 0 1
    rw [bordaP_four, bordaQ_four, ballot102_lt, ballot120_lt]
    decide

/-- Borda score reversal (C6): exhibits two profiles with identical per-voter
`0`-vs-`1` comparisons whose Borda scores of `0` and `1` reverse (a
score-reversal witness; Borda is not packaged as a `SocialWelfareFunction`
here, so no formal `IsIIA` negation is claimed). -/
theorem borda_score_reversal :
    ∃ P Q : Profile (Fin 3) (Fin 5),
      (∀ i : Fin 5, (P i).lt 0 1 ↔ (Q i).lt 0 1) ∧
        bordaScore P 1 < bordaScore P 0 ∧ bordaScore Q 0 < bordaScore Q 1 := by
  refine ⟨bordaP, bordaQ, borda_agreement, ?_, ?_⟩
  · rw [bordaScore_bordaP_one, bordaScore_bordaP_zero]
    decide
  · rw [bordaScore_bordaQ_zero, bordaScore_bordaQ_one]
    decide

end MathlibExt.GameTheory.SocialChoice

end
