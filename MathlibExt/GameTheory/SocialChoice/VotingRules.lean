/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module
public import MathlibExt.GameTheory.SocialChoice.Black
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
set_option autoImplicit false
namespace MathlibExt.GameTheory.SocialChoice
open Classical
open MathlibExt.Order
open MathlibExt.GameTheory.SocialChoice.ArrowWanted
open scoped BigOperators
@[expose] public section
/-- Net pairwise preference: voters ranking `a` above `b` minus voters
ranking `b` above `a`. -/
noncomputable def netPreference {Alt Voter : Type*} [Fintype Alt]
    [Fintype Voter] [DecidableEq Alt] (P : Profile Alt Voter) (a b : Alt) :
    ℤ :=
  (Finset.univ.filter fun i => (P i).lt a b).card -
    (Finset.univ.filter fun i => (P i).lt b a).card
/-- Pairwise majority preference: `a` beats `b` when its net preference is
positive. -/
def majorityPrefers {Alt Voter : Type*} [Fintype Alt] [Fintype Voter]
    [DecidableEq Alt] (P : Profile Alt Voter) (a b : Alt) : Prop :=
  0 < netPreference P a b
/-- Copeland score: pairwise majority wins minus losses. -/
noncomputable def copelandScore {Alt Voter : Type*} [Fintype Alt]
    [Fintype Voter] [DecidableEq Alt] (P : Profile Alt Voter) (a : Alt) :
    ℤ :=
  (Finset.univ.filter fun b => majorityPrefers P a b).card -
    (Finset.univ.filter fun b => majorityPrefers P b a).card
/-- Second-order Copeland score: the summed Copeland scores of the
alternatives that `a` beats pairwise. -/
noncomputable def secondOrderCopelandScore {Alt Voter : Type*} [Fintype Alt]
    [Fintype Voter] [DecidableEq Alt] (P : Profile Alt Voter) (a : Alt) :
    ℤ :=
  ∑ b ∈ Finset.univ.filter (fun b => majorityPrefers P a b),
    copelandScore P b
/-- The winner set of an integer score function: every alternative attaining
the maximal score. -/
noncomputable def winners {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    (s : Alt → ℤ) : Finset Alt :=
  Finset.univ.filter fun a => ∀ b, s b ≤ s a
/-- The number of alternatives ranked strictly above `a` in the order `r`
(the 0-based rank position of `a`). -/
noncomputable def rankAbove {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    (r : MathlibExt.Order.StrictTotalOrder Alt) (a : Alt) : ℕ :=
  (Finset.univ.filter fun b => r.lt b a).card
/-- Positional scoring score for the integer score vector `w` (0-based
positions): each voter awards `w k` points to the alternative they rank in
position `k`. -/
noncomputable def scoringScore {Alt Voter : Type*} [Fintype Alt]
    [Fintype Voter] [DecidableEq Alt] (w : ℕ → ℤ) (P : Profile Alt Voter)
    (a : Alt) : ℤ :=
  ∑ i, w (rankAbove (P i) a)
/-- Maximin (Simpson) score: the worst net pairwise preference of `a`
against any other alternative. -/
noncomputable def maximinScore {Alt Voter : Type*} [Fintype Alt]
    [Fintype Voter] [DecidableEq Alt] [Nontrivial Alt]
    (P : Profile Alt Voter) (a : Alt) : ℤ :=
  ((Finset.univ.erase a).image (netPreference P a)).min'
    (by
      obtain ⟨b, hb⟩ := exists_ne a
      exact ⟨netPreference P a b,
        Finset.mem_image.mpr ⟨b, Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩, rfl⟩⟩)
/-- Kendall tau distance between two strict total orders: the number of
ordered pairs on which they disagree (each unordered disagreement counts
once). -/
noncomputable def kendallTau {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    (r s : MathlibExt.Order.StrictTotalOrder Alt) : ℕ :=
  ((Finset.univ ×ˢ Finset.univ).filter
    fun p => r.lt p.1 p.2 ∧ s.lt p.2 p.1).card
/-- Kemeny score of a ranking: summed Kendall tau distance to the ballots. -/
noncomputable def kemenyScore {Alt Voter : Type*} [Fintype Alt]
    [Fintype Voter] [DecidableEq Alt] (P : Profile Alt Voter)
    (r : MathlibExt.Order.StrictTotalOrder Alt) : ℕ :=
  ∑ i, kendallTau (P i) r
/-- A Kemeny ranking minimizes the Kemeny score over all rankings. -/
def IsKemenyRanking {Alt Voter : Type*} [Fintype Alt] [Fintype Voter]
    [DecidableEq Alt] (P : Profile Alt Voter) (r : MathlibExt.Order.StrictTotalOrder Alt) :
    Prop :=
  ∀ s, kemenyScore P r ≤ kemenyScore P s
/-- A Condorcet winner beats every other alternative pairwise. -/
def IsCondorcetWinner {Alt Voter : Type*} [Fintype Alt] [Fintype Voter]
    [DecidableEq Alt] (P : Profile Alt Voter) (a : Alt) : Prop :=
  ∀ b, b ≠ a → majorityPrefers P a b
/-- Distance between profiles: summed per-voter Kendall tau distance. -/
noncomputable def profileDist {Alt Voter : Type*} [Fintype Alt]
    [Fintype Voter] [DecidableEq Alt] (P Q : Profile Alt Voter) : ℕ :=
  ∑ i, kendallTau (P i) (Q i)
/-- Dodgson score of `a`: the least profile distance to a profile in which
`a` is a Condorcet winner. -/
noncomputable def dodgsonScore {Alt Voter : Type*} [Fintype Alt]
    [Fintype Voter] [DecidableEq Alt] (P : Profile Alt Voter) (a : Alt) :
    ℕ :=
  ⨅ Q : {Q // IsCondorcetWinner Q a}, profileDist P Q.1
/-- Net preference of an alternative against itself is zero. -/
theorem netPreference_self {Alt Voter : Type*} [Fintype Alt] [Fintype Voter]
    [DecidableEq Alt] (P : Profile Alt Voter) (a : Alt) :
    netPreference P a a = 0 := by
  simp [netPreference]
/-- Net preference is antisymmetric in its alternative arguments. -/
theorem netPreference_antisymm {Alt Voter : Type*} [Fintype Alt]
    [Fintype Voter] [DecidableEq Alt] (P : Profile Alt Voter) (a b : Alt) :
    netPreference P a b = -netPreference P b a := by
  simp [netPreference]
/-- Kendall tau distance of a ranking to itself is zero. -/
theorem kendallTau_self {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    (r : MathlibExt.Order.StrictTotalOrder Alt) :
    kendallTau r r = 0 := by
  unfold kendallTau
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _ h
  obtain ⟨h1, h2⟩ := h
  exact r.irrefl p.1 (r.trans h1 h2)
/-- Kendall tau distance is symmetric. -/
theorem kendallTau_comm {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    (r s : MathlibExt.Order.StrictTotalOrder Alt) :
    kendallTau r s = kendallTau s r := by
  unfold kendallTau
  apply Finset.card_bij (fun p _ => (p.2, p.1))
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      true_and] at hp ⊢
    obtain ⟨h1, h2⟩ := hp
    exact ⟨h2, h1⟩
  · intro p1 _ p2 _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h2, h1⟩ := h
    exact Prod.ext h1 h2
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      true_and] at hq ⊢
    obtain ⟨h1, h2⟩ := hq
    exact ⟨(q.2, q.1), ⟨h2, h1⟩, rfl⟩
private theorem filterAboveBelow_disjoint {Alt : Type*} [Fintype Alt]
    [DecidableEq Alt] (r : MathlibExt.Order.StrictTotalOrder Alt)
    (a : Alt) :
    Disjoint (Finset.univ.filter fun b => r.lt b a)
      (Finset.univ.filter fun b => r.lt a b) := by
  rw [Finset.disjoint_left]
  intro b hb1 hb2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb1 hb2
  exact r.irrefl b (r.trans hb1 hb2)
private theorem filterAboveBelow_union {Alt : Type*} [Fintype Alt]
    [DecidableEq Alt] (r : MathlibExt.Order.StrictTotalOrder Alt)
    (a : Alt) :
    (Finset.univ.filter fun b => r.lt b a) ∪
        (Finset.univ.filter fun b => r.lt a b) =
      Finset.univ.erase a := by
  ext b
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro (h | h) rfl
    · exact r.irrefl _ h
    · exact r.irrefl _ h
  · intro h
    exact r.total h
private theorem rankAbove_add_below {Alt : Type*} [Fintype Alt]
    [DecidableEq Alt] (r : MathlibExt.Order.StrictTotalOrder Alt)
    (a : Alt) :
    rankAbove r a + (Finset.univ.filter fun b => r.lt a b).card =
      Fintype.card Alt - 1 := by
  have hdisj := filterAboveBelow_disjoint r a
  have hunion := filterAboveBelow_union r a
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion] at hcard
  rw [Finset.card_erase_of_mem (Finset.mem_univ a)] at hcard
  unfold rankAbove
  exact hcard.symm
private theorem bordaWeight_eq {Alt : Type*} [Fintype Alt]
    [DecidableEq Alt] (r : MathlibExt.Order.StrictTotalOrder Alt)
    (a : Alt) :
    (Fintype.card Alt : ℤ) - 1 - (rankAbove r a : ℤ) =
      ((Finset.univ.filter fun b => r.lt a b).card : ℤ) := by
  have hsum := rankAbove_add_below r a
  have hpos : 0 < Fintype.card Alt :=
    Finset.card_pos.mpr ⟨a, Finset.mem_univ a⟩
  have hle : 1 ≤ Fintype.card Alt := hpos
  have hC1 : ((Fintype.card Alt - 1 : ℕ) : ℤ) =
      (Fintype.card Alt : ℤ) - 1 := by
    rw [Nat.cast_sub hle, Nat.cast_one]
  have hcast : (rankAbove r a : ℤ) +
      ((Finset.univ.filter fun b => r.lt a b).card : ℤ) =
      (Fintype.card Alt : ℤ) - 1 := by
    rw [← Nat.cast_add, hsum, hC1]
  rw [← hcast, add_sub_cancel_left]
/-- The Borda score is the positional scoring score for the Borda vector. -/
theorem scoringScore_bordaVector {Alt Voter : Type*} [Fintype Alt]
    [Fintype Voter] [DecidableEq Alt] (P : Profile Alt Voter) (a : Alt) :
    scoringScore (fun k => (Fintype.card Alt : ℤ) - 1 - k) P a =
      (bordaScore P a : ℤ) := by
  unfold scoringScore bordaScore
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact bordaWeight_eq (P i) a
private noncomputable def equivFinOrder {Alt : Type*} [Fintype Alt] :
    MathlibExt.Order.StrictTotalOrder Alt where
  lt := fun a b => Fintype.equivFin Alt a < Fintype.equivFin Alt b
  irrefl := fun a => lt_irrefl (Fintype.equivFin Alt a)
  trans := fun {a b c} h1 h2 => lt_trans h1 h2
  total := fun {a b} h => by
    have hne : Fintype.equivFin Alt a ≠ Fintype.equivFin Alt b :=
      (Fintype.equivFin Alt).injective.ne h
    have htri := lt_or_gt_of_ne hne
    cases htri with
    | inl hlt => exact Or.inl hlt
    | inr hgt => exact Or.inr hgt
/-- A Kemeny ranking always exists. -/
theorem exists_isKemenyRanking {Alt Voter : Type*} [Fintype Alt]
    [Fintype Voter] [DecidableEq Alt] (P : Profile Alt Voter) :
    ∃ r, IsKemenyRanking P r := by
  have hex : ∃ n, ∃ r, kemenyScore P r = n :=
    ⟨kemenyScore P equivFinOrder, equivFinOrder, rfl⟩
  have hspec := Nat.find_spec hex
  obtain ⟨r, hr⟩ := hspec
  refine ⟨r, fun s => ?_⟩
  rw [hr]
  exact Nat.find_min' hex ⟨s, rfl⟩
end
end MathlibExt.GameTheory.SocialChoice
