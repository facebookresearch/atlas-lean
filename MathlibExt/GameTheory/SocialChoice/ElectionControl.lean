/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module
public import MathlibExt.GameTheory.SocialChoice.VotingRules
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
set_option autoImplicit false
namespace MathlibExt.GameTheory.SocialChoice
open Classical
open MathlibExt.Order
open MathlibExt.GameTheory.SocialChoice.ArrowWanted
open scoped BigOperators
@[expose] public section
/-!
# Control by adding or deleting candidates

Restricting an election to a subset of candidates restricts every ballot and
leaves pairwise margins among the remaining candidates unchanged. A Condorcet
winner therefore stays a Condorcet winner under restriction, so constructive
control by adding candidates can never succeed. Deleting candidates can
succeed: in a three-candidate cycle, deleting one candidate makes another the
Condorcet winner.

## Main results

* `not_canControlByAddingCandidates`: immunity to control by adding candidates.
* `exists_controlByDeletingCandidates`: susceptibility to control by deleting
  candidates, witnessed by a 3-cycle.

## References

* P. Faliszewski and J. Rothe, *Handbook of Computational Social Choice*,
  Chapter 7, Definition 7.1 and Theorem 7.3.
-/
/-- The restriction of a strict total order to a finset of alternatives,
as an order on the subtype. -/
def restrictOrder {Alt : Type*} (r : MathlibExt.Order.StrictTotalOrder Alt)
    (S : Finset Alt) : MathlibExt.Order.StrictTotalOrder {a // a ∈ S} where
  lt a b := r.lt a.1 b.1
  irrefl a := r.irrefl a.1
  trans h1 h2 := r.trans h1 h2
  total h := r.total fun heq => h (Subtype.ext heq)
/-- The election restricted to the candidates in `S`: every ballot
restricted to `S`. -/
def restrictProfile {Alt Voter : Type*} (P : Profile Alt Voter)
    (S : Finset Alt) : Profile {a // a ∈ S} Voter :=
  fun i => restrictOrder (P i) S
/-- Constructive control by adding candidates succeeds for `p` in the
election `P` over `Alt` with registered candidate set `S` and budget `k`:
`p` is registered but not the Condorcet winner of the registered election,
and adding at most `k` further candidates of `Alt` (reaching a set `S'`)
makes `p` the Condorcet winner there. -/
def CanControlByAddingCandidates {Alt Voter : Type*} [Fintype Alt]
    [Fintype Voter] [DecidableEq Alt] (P : Profile Alt Voter)
    (S : Finset Alt) (p : Alt) (k : ℕ) : Prop :=
  ∃ (hp : p ∈ S) (S' : Finset Alt) (hsub : S ⊆ S'), S'.card ≤ S.card + k ∧
    ¬ IsCondorcetWinner (restrictProfile P S) ⟨p, hp⟩ ∧
      IsCondorcetWinner (restrictProfile P S') ⟨p, hsub hp⟩
/-- Pairwise margins are unchanged by restricting the candidate set. -/
theorem netPreference_restrictProfile {Alt Voter : Type*} [Fintype Alt]
    [Fintype Voter] [DecidableEq Alt] (P : Profile Alt Voter)
    (S : Finset Alt) (a b : {x // x ∈ S}) :
    netPreference (restrictProfile P S) a b = netPreference P a.1 b.1 :=
  rfl
/-- With finitely many candidates and voters, a Condorcet winner of the full election is the
Condorcet winner of every restricted election still containing them. -/
theorem isCondorcetWinner_restrictProfile {Alt Voter : Type*}
    [Fintype Alt] [Fintype Voter] [DecidableEq Alt] (P : Profile Alt Voter)
    (S : Finset Alt) {p : Alt} (hp : p ∈ S) (h : IsCondorcetWinner P p) :
    IsCondorcetWinner (restrictProfile P S) ⟨p, hp⟩ := by
  intro b hb
  have hne : b.1 ≠ p := fun heq => hb (Subtype.ext heq)
  have hw := h b.1 hne
  rw [majorityPrefers_iff_netPreference_pos] at hw ⊢
  rw [netPreference_restrictProfile]
  exact hw
/-- A Condorcet winner of an election restricted to `T` is the Condorcet
winner of every election restricted to a subset `S ⊆ T` still containing
them. -/
private theorem isCondorcetWinner_restrictProfile_of_subset {Alt Voter : Type*}
    [Fintype Alt] [Fintype Voter] [DecidableEq Alt] (P : Profile Alt Voter)
    (S T : Finset Alt) (hsub : S ⊆ T) {p : Alt} (hpS : p ∈ S)
    (h : IsCondorcetWinner (restrictProfile P T) ⟨p, hsub hpS⟩) :
    IsCondorcetWinner (restrictProfile P S) ⟨p, hpS⟩ := by
  intro b hb
  have hne : (⟨b.1, hsub b.2⟩ : {x // x ∈ T}) ≠ ⟨p, hsub hpS⟩ := by
    intro heq
    apply hb
    have hval : b.1 = p := congrArg Subtype.val heq
    exact Subtype.ext hval
  have hw := h ⟨b.1, hsub b.2⟩ hne
  rw [majorityPrefers_iff_netPreference_pos] at hw ⊢
  rw [netPreference_restrictProfile] at hw
  rw [netPreference_restrictProfile]
  exact hw
/-- **Immunity of Condorcet voting to constructive control by adding
candidates** (Theorem 7.3(1)): control by adding candidates can never
succeed for any preferred candidate, registered set, or budget. -/
theorem not_canControlByAddingCandidates {Alt Voter : Type*} [Fintype Alt]
    [Fintype Voter] [DecidableEq Alt] (P : Profile Alt Voter)
    (S : Finset Alt) (p : Alt) (k : ℕ) :
    ¬ CanControlByAddingCandidates P S p k := by
  intro hcon
  obtain ⟨hp, S', hsub, _hle, hnot, hwin⟩ := hcon
  exact hnot
    (isCondorcetWinner_restrictProfile_of_subset P S S' hsub hp hwin)
private def cycleRank (i a : Fin 3) : ℕ := (a.val + 3 - i.val) % 3
private theorem cycleRank_injective_all :
    ∀ (i a b : Fin 3), cycleRank i a = cycleRank i b → a = b := by decide
private theorem cycleRank_injective (i : Fin 3) :
    Function.Injective (cycleRank i) :=
  fun _ _ h => cycleRank_injective_all i _ _ h
private def cycleOrder (i : Fin 3) : MathlibExt.Order.StrictTotalOrder (Fin 3) where
  lt := fun a b => cycleRank i a < cycleRank i b
  irrefl := fun a => Nat.lt_irrefl _
  trans := fun h1 h2 => Nat.lt_trans h1 h2
  total := fun {a b} hne => by
    have hRne : cycleRank i a ≠ cycleRank i b :=
      fun h => hne (cycleRank_injective i h)
    exact lt_or_gt_of_ne hRne
private def cycleP : Profile (Fin 3) (Fin 3) := fun i => cycleOrder i
private theorem cycleP_filter_01 :
    Finset.univ.filter (fun i : Fin 3 => (cycleP i).lt 0 1) = {0, 2} := by
  have hcongr : Finset.univ.filter (fun i : Fin 3 => (cycleP i).lt 0 1)
      = Finset.univ.filter (fun i : Fin 3 => cycleRank i 0 < cycleRank i 1) :=
    Finset.filter_congr (fun i _ => Iff.rfl)
  rw [hcongr]
  decide
private theorem cycleP_filter_10 :
    Finset.univ.filter (fun i : Fin 3 => (cycleP i).lt 1 0) = {1} := by
  have hcongr : Finset.univ.filter (fun i : Fin 3 => (cycleP i).lt 1 0)
      = Finset.univ.filter (fun i : Fin 3 => cycleRank i 1 < cycleRank i 0) :=
    Finset.filter_congr (fun i _ => Iff.rfl)
  rw [hcongr]
  decide
private theorem cycleP_filter_02 :
    Finset.univ.filter (fun i : Fin 3 => (cycleP i).lt 0 2) = {0} := by
  have hcongr : Finset.univ.filter (fun i : Fin 3 => (cycleP i).lt 0 2)
      = Finset.univ.filter (fun i : Fin 3 => cycleRank i 0 < cycleRank i 2) :=
    Finset.filter_congr (fun i _ => Iff.rfl)
  rw [hcongr]
  decide
private theorem cycleP_filter_20 :
    Finset.univ.filter (fun i : Fin 3 => (cycleP i).lt 2 0) = {1, 2} := by
  have hcongr : Finset.univ.filter (fun i : Fin 3 => (cycleP i).lt 2 0)
      = Finset.univ.filter (fun i : Fin 3 => cycleRank i 2 < cycleRank i 0) :=
    Finset.filter_congr (fun i _ => Iff.rfl)
  rw [hcongr]
  decide
private theorem cycleP_card_01 :
    (Finset.univ.filter (fun i : Fin 3 => (cycleP i).lt 0 1)).card = 2 := by
  rw [cycleP_filter_01]
  decide
private theorem cycleP_card_10 :
    (Finset.univ.filter (fun i : Fin 3 => (cycleP i).lt 1 0)).card = 1 := by
  rw [cycleP_filter_10]
  decide
private theorem cycleP_card_02 :
    (Finset.univ.filter (fun i : Fin 3 => (cycleP i).lt 0 2)).card = 1 := by
  rw [cycleP_filter_02]
  decide
private theorem cycleP_card_20 :
    (Finset.univ.filter (fun i : Fin 3 => (cycleP i).lt 2 0)).card = 2 := by
  rw [cycleP_filter_20]
  decide
private theorem cycleP_margin_01 : netPreference cycleP 0 1 = 1 := by
  simp only [netPreference]
  rw [cycleP_card_01, cycleP_card_10]
  decide
private theorem cycleP_margin_02 : netPreference cycleP 0 2 = -1 := by
  simp only [netPreference]
  rw [cycleP_card_02, cycleP_card_20]
  decide
/-- **Susceptibility to constructive control by deleting candidates**
(Theorem 7.3(2), susceptibility part): some election has no Condorcet
winner `p`, yet deleting candidates (restricting to a subset still
containing `p`) makes `p` the Condorcet winner. The witness is a
3-cycle. -/
theorem exists_controlByDeletingCandidates :
    ∃ (P : Profile (Fin 3) (Fin 3)) (p : Fin 3) (S : Finset (Fin 3))
      (hp : p ∈ S),
      ¬ IsCondorcetWinner P p ∧
        IsCondorcetWinner (restrictProfile P S) ⟨p, hp⟩ ∧ S.card = 2 := by
  refine ⟨cycleP, 0, {0, 1}, by decide, ?_, ?_, ?_⟩
  · intro h
    have h2 := h 2 (by decide)
    rw [majorityPrefers_iff_netPreference_pos] at h2
    rw [cycleP_margin_02] at h2
    omega
  · intro b hb
    have hmem : b.1 = 0 ∨ b.1 = 1 := by
      have h2 := b.2
      simp only [Finset.mem_insert, Finset.mem_singleton] at h2
      exact h2
    have hval : b.1 = 1 := by
      cases hmem with
      | inl h0 =>
        exfalso
        apply hb
        exact Subtype.ext h0
      | inr h1 => exact h1
    rw [majorityPrefers_iff_netPreference_pos]
    rw [netPreference_restrictProfile]
    show 0 < netPreference cycleP 0 b.1
    rw [hval, cycleP_margin_01]
    decide
  · decide
end
end MathlibExt.GameTheory.SocialChoice
