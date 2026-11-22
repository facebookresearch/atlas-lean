/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.GameTheory.SocialChoice.VotingRules
public import Mathlib.Data.Fintype.Prod

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.BigOperators

/-!
# McGarvey realization of tournaments with ties

Every irreflexive, asymmetric pairwise relation on a finite
alternative set is the strict-majority relation of a profile of
strict total orders, with every decided contest decided by margin
exactly `2` and every tie tied exactly. The construction uses two
voters per directed edge: for an edge `a ≻ b`, one ballot ranks
`a` above `b` above the remaining alternatives in a fixed order,
and the other ranks the remaining alternatives in the reverse
order above `a` above `b`; on every other pair the two ballots
cancel.

References: D. C. McGarvey, "A theorem on the construction of
voting paradoxes", *Econometrica* 21 (1953), 608–610; the
margin-two interface is the one consumed by J. Bartholdi III,
C. A. Tovey and M. A. Trick, "The computational difficulty of
manipulating an election", *Social Choice and Welfare* 6 (1989),
227–241.
-/

set_option autoImplicit false

namespace MathlibExt.GameTheory.SocialChoice

open MathlibExt.GameTheory.SocialChoice.ArrowWanted
open scoped Classical BigOperators

@[expose] public section

/-- Fixed enumeration rank of an alternative. -/
private noncomputable def mcgRank {Alt : Type*} [Fintype Alt] [DecidableEq Alt] (a : Alt) : ℕ :=
  (Fintype.equivFin Alt a).val

private theorem mcgRank_lt_card {Alt : Type*} [Fintype Alt] [DecidableEq Alt] (a : Alt) :
    mcgRank a < Fintype.card Alt :=
  (Fintype.equivFin Alt a).isLt

private theorem mcgRank_inj {Alt : Type*} [Fintype Alt] [DecidableEq Alt] :
    Function.Injective (mcgRank (Alt := Alt)) := by
  intro a b h
  exact (Fintype.equivFin Alt).injective (Fin.ext h)

/-- First ballot key for a directed edge: the head above the tail above the rest. -/
private noncomputable def keyF {Alt : Type*} [Fintype Alt] [DecidableEq Alt] (x y a : Alt) : ℕ :=
  if a = x then 0 else if a = y then 1 else mcgRank a + 2

/-- Second ballot key for a directed edge: the rest in reverse rank order above head and tail. -/
private noncomputable def keyT {Alt : Type*} [Fintype Alt] [DecidableEq Alt] (x y a : Alt) : ℕ :=
  if a = x then Fintype.card Alt
  else if a = y then Fintype.card Alt + 1
  else (Fintype.card Alt - 1 - mcgRank a)

private theorem injective_keyF {Alt : Type*} [Fintype Alt] [DecidableEq Alt] (x y : Alt) :
    Function.Injective (keyF x y) := by
  intro a b h
  simp only [keyF] at h
  by_cases hax : a = x
  · rw [ite_eq_left hax] at h
    by_cases hbx : b = x
    · rw [ite_eq_left hbx] at h
      exact hax.trans hbx.symm
    · rw [ite_eq_right hbx] at h
      by_cases hby : b = y
      · rw [ite_eq_left hby] at h
        have hF : False := by omega
        exact hF.elim
      · rw [ite_eq_right hby] at h
        have hF : False := by omega
        exact hF.elim
  · rw [ite_eq_right hax] at h
    by_cases hay : a = y
    · rw [ite_eq_left hay] at h
      by_cases hbx : b = x
      · rw [ite_eq_left hbx] at h
        have hF : False := by omega
        exact hF.elim
      · rw [ite_eq_right hbx] at h
        by_cases hby : b = y
        · rw [ite_eq_left hby] at h
          exact hay.trans hby.symm
        · rw [ite_eq_right hby] at h
          have hF : False := by omega
          exact hF.elim
    · rw [ite_eq_right hay] at h
      by_cases hbx : b = x
      · rw [ite_eq_left hbx] at h
        have hF : False := by omega
        exact hF.elim
      · rw [ite_eq_right hbx] at h
        by_cases hby : b = y
        · rw [ite_eq_left hby] at h
          have hF : False := by omega
          exact hF.elim
        · rw [ite_eq_right hby] at h
          have hr : mcgRank a = mcgRank b := by omega
          exact mcgRank_inj hr

private theorem injective_keyT {Alt : Type*} [Fintype Alt] [DecidableEq Alt] (x y : Alt) :
    Function.Injective (keyT x y) := by
  intro a b h
  have hra : mcgRank a < Fintype.card Alt := mcgRank_lt_card a
  have hrb : mcgRank b < Fintype.card Alt := mcgRank_lt_card b
  simp only [keyT] at h
  by_cases hax : a = x
  · rw [ite_eq_left hax] at h
    by_cases hbx : b = x
    · rw [ite_eq_left hbx] at h
      exact hax.trans hbx.symm
    · rw [ite_eq_right hbx] at h
      by_cases hby : b = y
      · rw [ite_eq_left hby] at h
        have hF : False := by omega
        exact hF.elim
      · rw [ite_eq_right hby] at h
        have hF : False := by omega
        exact hF.elim
  · rw [ite_eq_right hax] at h
    by_cases hay : a = y
    · rw [ite_eq_left hay] at h
      by_cases hbx : b = x
      · rw [ite_eq_left hbx] at h
        have hF : False := by omega
        exact hF.elim
      · rw [ite_eq_right hbx] at h
        by_cases hby : b = y
        · rw [ite_eq_left hby] at h
          exact hay.trans hby.symm
        · rw [ite_eq_right hby] at h
          have hF : False := by omega
          exact hF.elim
    · rw [ite_eq_right hay] at h
      by_cases hbx : b = x
      · rw [ite_eq_left hbx] at h
        have hF : False := by omega
        exact hF.elim
      · rw [ite_eq_right hbx] at h
        by_cases hby : b = y
        · rw [ite_eq_left hby] at h
          have hF : False := by omega
          exact hF.elim
        · rw [ite_eq_right hby] at h
          have hr : mcgRank a = mcgRank b := by omega
          exact mcgRank_inj hr

/-- Ballot from an injective key. -/
private def ballotOf {Alt : Type*} (k : Alt → ℕ) (hinj : Function.Injective k) :
    _root_.MathlibExt.Order.StrictTotalOrder Alt :=
  { lt := fun a b => k a < k b
    irrefl := fun _ => lt_irrefl _
    trans := fun h1 h2 => lt_trans h1 h2
    total := fun hne => lt_or_gt_of_ne (fun h => hne (hinj h)) }

/-- The two ballots of one directed edge gadget. -/
private noncomputable def mcgBallot {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    (beats : Alt → Alt → Prop) (e : {p : Alt × Alt // beats p.1 p.2}) :
    Bool → _root_.MathlibExt.Order.StrictTotalOrder Alt
  | false => ballotOf (keyF e.1.1 e.1.2) (injective_keyF e.1.1 e.1.2)
  | true => ballotOf (keyT e.1.1 e.1.2) (injective_keyT e.1.1 e.1.2)

/-- The McGarvey profile: two voters per directed edge. -/
private noncomputable def mcgProfile {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    (beats : Alt → Alt → Prop) [DecidableRel beats] :
    Profile Alt ({p : Alt × Alt // beats p.1 p.2} × Bool) :=
  fun i => mcgBallot beats i.1 i.2

private theorem P_lt_false {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    (beats : Alt → Alt → Prop) [DecidableRel beats]
    (e : {p : Alt × Alt // beats p.1 p.2}) (a b : Alt) :
    (mcgProfile beats (e, false)).lt a b = (keyF e.1.1 e.1.2 a < keyF e.1.1 e.1.2 b) := rfl

private theorem P_lt_true {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    (beats : Alt → Alt → Prop) [DecidableRel beats]
    (e : {p : Alt × Alt // beats p.1 p.2}) (a b : Alt) :
    (mcgProfile beats (e, true)).lt a b = (keyT e.1.1 e.1.2 a < keyT e.1.1 e.1.2 b) := rfl

private theorem edge_ne_of_beats {Alt : Type*} (beats : Alt → Alt → Prop)
    (hirrefl : ∀ a, ¬ beats a a) {x y : Alt} (h : beats x y) : x ≠ y := by
  intro hcon
  subst hcon
  exact hirrefl _ h

/-- The gadget for `(a, b)` contributes `+2` to the `(a, b)` margin. -/
private theorem inner_two {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    (beats : Alt → Alt → Prop) [DecidableRel beats]
    {a b : Alt} (hne : a ≠ b) (e : {p : Alt × Alt // beats p.1 p.2})
    (hx : e.1.1 = a) (hy : e.1.2 = b) :
    (∑ flag : Bool, (if (mcgProfile beats (e, flag)).lt a b then (1:ℤ) else -1)) = 2 := by
  simp only [Fintype.sum_bool]
  rw [P_lt_false, P_lt_true, hx, hy]
  have hba : b ≠ a := fun h => hne h.symm
  have k1 : keyF a b a = 0 := by unfold keyF; rw [ite_eq_left rfl]
  have k2 : keyF a b b = 1 := by unfold keyF; rw [ite_eq_right hba, ite_eq_left rfl]
  have k3 : keyT a b a = Fintype.card Alt := by unfold keyT; rw [ite_eq_left rfl]
  have k4 : keyT a b b = Fintype.card Alt + 1 := by
    unfold keyT; rw [ite_eq_right hba, ite_eq_left rfl]
  have cF : keyF a b a < keyF a b b := by omega
  have cT : keyT a b a < keyT a b b := by omega
  rw [ite_eq_left cF, ite_eq_left cT]
  norm_num

/-- The gadget for `(b, a)` contributes `-2` to the `(a, b)` margin. -/
private theorem inner_neg_two {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    (beats : Alt → Alt → Prop) [DecidableRel beats]
    {a b : Alt} (hne : a ≠ b) (e : {p : Alt × Alt // beats p.1 p.2})
    (hx : e.1.1 = b) (hy : e.1.2 = a) :
    (∑ flag : Bool, (if (mcgProfile beats (e, flag)).lt a b then (1:ℤ) else -1)) = -2 := by
  simp only [Fintype.sum_bool]
  rw [P_lt_false, P_lt_true, hx, hy]
  have k1 : keyF b a a = 1 := by unfold keyF; rw [ite_eq_right hne, ite_eq_left rfl]
  have k2 : keyF b a b = 0 := by unfold keyF; rw [ite_eq_left rfl]
  have k3 : keyT b a a = Fintype.card Alt + 1 := by
    unfold keyT; rw [ite_eq_right hne, ite_eq_left rfl]
  have k4 : keyT b a b = Fintype.card Alt := by unfold keyT; rw [ite_eq_left rfl]
  have cF : ¬ keyF b a a < keyF b a b := by omega
  have cT : ¬ keyT b a a < keyT b a b := by omega
  rw [ite_eq_right cF, ite_eq_right cT]
  norm_num

/-- Every other gadget contributes `0` to the `(a, b)` margin: its two ballots cancel. -/
private theorem inner_zero {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    (beats : Alt → Alt → Prop) [DecidableRel beats]
    (hirrefl : ∀ a, ¬ beats a a) {a b : Alt} (hne : a ≠ b)
    (e : {p : Alt × Alt // beats p.1 p.2}) (x y : Alt)
    (hx : e.1.1 = x) (hy : e.1.2 = y)
    (h1 : (x, y) ≠ (a, b)) (h2 : (x, y) ≠ (b, a)) :
    (∑ flag : Bool, (if (mcgProfile beats (e, flag)).lt a b then (1:ℤ) else -1)) = 0 := by
  have hbeats : beats x y := by rw [← hx, ← hy]; exact e.property
  have hxy : x ≠ y := edge_ne_of_beats beats hirrefl hbeats
  simp only [Fintype.sum_bool]
  rw [P_lt_false, P_lt_true, hx, hy]
  by_cases hax : a = x
  · by_cases hay : a = y
    · exact (hxy (hax.symm.trans hay)).elim
    · by_cases hbx : b = x
      · exact (hne (hax.trans hbx.symm)).elim
      · by_cases hby : b = y
        · exact (h1 (Prod.ext hax.symm hby.symm)).elim
        · have hrb : mcgRank b < Fintype.card Alt := mcgRank_lt_card b
          have kaF : keyF x y a = 0 := by unfold keyF; rw [ite_eq_left hax]
          have kbF : keyF x y b = mcgRank b + 2 := by
            unfold keyF; rw [ite_eq_right hbx, ite_eq_right hby]
          have kaT : keyT x y a = Fintype.card Alt := by unfold keyT; rw [ite_eq_left hax]
          have kbT : keyT x y b = Fintype.card Alt - 1 - mcgRank b := by
            unfold keyT; rw [ite_eq_right hbx, ite_eq_right hby]
          have cF : keyF x y a < keyF x y b := by omega
          have cT : ¬ keyT x y a < keyT x y b := by omega
          rw [ite_eq_left cF, ite_eq_right cT]
          norm_num
  · by_cases hay : a = y
    · by_cases hbx : b = x
      · exact (h2 (Prod.ext hbx.symm hay.symm)).elim
      · by_cases hby : b = y
        · exact (hne (hay.trans hby.symm)).elim
        · have hrb : mcgRank b < Fintype.card Alt := mcgRank_lt_card b
          have kaF : keyF x y a = 1 := by unfold keyF; rw [ite_eq_right hax, ite_eq_left hay]
          have kbF : keyF x y b = mcgRank b + 2 := by
            unfold keyF; rw [ite_eq_right hbx, ite_eq_right hby]
          have kaT : keyT x y a = Fintype.card Alt + 1 := by
            unfold keyT; rw [ite_eq_right hax, ite_eq_left hay]
          have kbT : keyT x y b = Fintype.card Alt - 1 - mcgRank b := by
            unfold keyT; rw [ite_eq_right hbx, ite_eq_right hby]
          have cF : keyF x y a < keyF x y b := by omega
          have cT : ¬ keyT x y a < keyT x y b := by omega
          rw [ite_eq_left cF, ite_eq_right cT]
          norm_num
    · by_cases hbx : b = x
      · by_cases hby : b = y
        · exact (hxy (hbx.symm.trans hby)).elim
        · have hra : mcgRank a < Fintype.card Alt := mcgRank_lt_card a
          have kaF : keyF x y a = mcgRank a + 2 := by
            unfold keyF; rw [ite_eq_right hax, ite_eq_right hay]
          have kbF : keyF x y b = 0 := by unfold keyF; rw [ite_eq_left hbx]
          have kaT : keyT x y a = Fintype.card Alt - 1 - mcgRank a := by
            unfold keyT; rw [ite_eq_right hax, ite_eq_right hay]
          have kbT : keyT x y b = Fintype.card Alt := by unfold keyT; rw [ite_eq_left hbx]
          have cF : ¬ keyF x y a < keyF x y b := by omega
          have cT : keyT x y a < keyT x y b := by omega
          rw [ite_eq_right cF, ite_eq_left cT]
          norm_num
      · by_cases hby : b = y
        · have hra : mcgRank a < Fintype.card Alt := mcgRank_lt_card a
          have kaF : keyF x y a = mcgRank a + 2 := by
            unfold keyF; rw [ite_eq_right hax, ite_eq_right hay]
          have kbF : keyF x y b = 1 := by unfold keyF; rw [ite_eq_right hbx, ite_eq_left hby]
          have kaT : keyT x y a = Fintype.card Alt - 1 - mcgRank a := by
            unfold keyT; rw [ite_eq_right hax, ite_eq_right hay]
          have kbT : keyT x y b = Fintype.card Alt + 1 := by
            unfold keyT; rw [ite_eq_right hbx, ite_eq_left hby]
          have cF : ¬ keyF x y a < keyF x y b := by omega
          have cT : keyT x y a < keyT x y b := by omega
          rw [ite_eq_right cF, ite_eq_left cT]
          norm_num
        · have hra : mcgRank a < Fintype.card Alt := mcgRank_lt_card a
          have hrb : mcgRank b < Fintype.card Alt := mcgRank_lt_card b
          have hrne : mcgRank a ≠ mcgRank b := fun h => hne (mcgRank_inj h)
          have kaF : keyF x y a = mcgRank a + 2 := by
            unfold keyF; rw [ite_eq_right hax, ite_eq_right hay]
          have kbF : keyF x y b = mcgRank b + 2 := by
            unfold keyF; rw [ite_eq_right hbx, ite_eq_right hby]
          have kaT : keyT x y a = Fintype.card Alt - 1 - mcgRank a := by
            unfold keyT; rw [ite_eq_right hax, ite_eq_right hay]
          have kbT : keyT x y b = Fintype.card Alt - 1 - mcgRank b := by
            unfold keyT; rw [ite_eq_right hbx, ite_eq_right hby]
          rcases lt_or_gt_of_ne hrne with hlt | hgt
          · have cF : keyF x y a < keyF x y b := by omega
            have cT : ¬ keyT x y a < keyT x y b := by omega
            rw [ite_eq_left cF, ite_eq_right cT]
            norm_num
          · have cF : ¬ keyF x y a < keyF x y b := by omega
            have cT : keyT x y a < keyT x y b := by omega
            rw [ite_eq_right cF, ite_eq_left cT]
            norm_num

/-- The net preference is the sum of per-voter signs. -/
private theorem sum_sign_eq_netPreference {Alt Voter : Type*} [Fintype Alt] [Fintype Voter]
    [DecidableEq Alt] (P : Profile Alt Voter) {a b : Alt} (hne : a ≠ b) :
    (∑ i : Voter, (if (P i).lt a b then (1:ℤ) else -1)) = netPreference P a b := by
  have hiff : ∀ i : Voter, (¬ (P i).lt a b) ↔ (P i).lt b a := fun i =>
    ⟨fun hnc => ((P i).total hne).resolve_left hnc,
     fun hd hc => (P i).irrefl a ((P i).trans hc hd)⟩
  have h1 : (∑ i ∈ Finset.univ.filter (fun i => (P i).lt a b),
        (if (P i).lt a b then (1:ℤ) else -1)) =
      ((Finset.univ.filter (fun i => (P i).lt a b)).card : ℤ) := by
    trans ∑ i ∈ Finset.univ.filter (fun i => (P i).lt a b), (1 : ℤ)
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      exact ite_eq_left (Finset.mem_filter.mp hi).2
    · simp
  have h2 : (∑ i ∈ Finset.univ.filter (fun i => ¬ (P i).lt a b),
        (if (P i).lt a b then (1:ℤ) else -1)) =
      -((Finset.univ.filter (fun i => ¬ (P i).lt a b)).card : ℤ) := by
    trans ∑ i ∈ Finset.univ.filter (fun i => ¬ (P i).lt a b), (-1 : ℤ)
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      exact ite_eq_right (Finset.mem_filter.mp hi).2
    · simp
  have hsame : Finset.univ.filter (fun i => ¬ (P i).lt a b) =
      Finset.univ.filter (fun i => (P i).lt b a) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hiff i
  have hpart : (∑ i ∈ Finset.univ.filter (fun i => (P i).lt a b),
        (if (P i).lt a b then (1:ℤ) else -1)) +
      (∑ i ∈ Finset.univ.filter (fun i => ¬ (P i).lt a b),
        (if (P i).lt a b then (1:ℤ) else -1)) =
      (∑ i : Voter, (if (P i).lt a b then (1:ℤ) else -1)) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  rw [h1, h2] at hpart
  have hcard : ((Finset.univ.filter (fun i => ¬ (P i).lt a b)).card : ℤ) =
      ((Finset.univ.filter (fun i => (P i).lt b a)).card : ℤ) := by rw [hsame]
  simp only [netPreference]
  rw [← hpart]
  omega

/-- **McGarvey realization.** For every irreflexive asymmetric
relation `beats` on a finite alternative set, the profile with two
voters per directed edge realizes `beats` with margin exactly `2`
on decided pairs and margin `0` on tied pairs. -/
theorem exists_profile_netPreference_eq_of_beats {Alt : Type*}
    [Fintype Alt] [DecidableEq Alt] (beats : Alt → Alt → Prop)
    [DecidableRel beats] (hirrefl : ∀ a, ¬ beats a a)
    (hasym : ∀ {a b}, beats a b → ¬ beats b a) :
    ∃ P : Profile Alt
        ({p : Alt × Alt // beats p.1 p.2} × Bool),
      ∀ a b, a ≠ b →
        netPreference P a b =
          if beats a b then 2 else if beats b a then -2 else 0 := by
  refine ⟨mcgProfile beats, fun a b hne => ?_⟩
  have hsign : (∑ i : {p : Alt × Alt // beats p.1 p.2} × Bool,
        (if (mcgProfile beats i).lt a b then (1:ℤ) else -1)) =
      netPreference (mcgProfile beats) a b :=
    sum_sign_eq_netPreference (mcgProfile beats) hne
  rw [← hsign]
  simp only [Fintype.sum_prod_type]
  by_cases hab : beats a b
  · rw [ite_eq_left hab]
    have hzero : ∀ e' ∈ (Finset.univ : Finset {p : Alt × Alt // beats p.1 p.2}),
        e' ≠ (⟨(a, b), hab⟩ : {p : Alt × Alt // beats p.1 p.2}) →
        (∑ flag : Bool,
          (if (mcgProfile beats (e', flag)).lt a b then (1:ℤ) else -1)) = 0 := by
      intro e' _ hne'
      obtain ⟨⟨x, y⟩, hxy⟩ := e'
      have h1 : (x, y) ≠ (a, b) := fun hcon => hne' (Subtype.ext hcon)
      by_cases h2 : (x, y) = (b, a)
      · exfalso
        have hxy' : beats x y := hxy
        have hbx : x = b := congrArg Prod.fst h2
        have hya : y = a := congrArg Prod.snd h2
        rw [hbx, hya] at hxy'
        exact hasym hab hxy'
      · exact inner_zero beats hirrefl hne (⟨(x, y), hxy⟩ :
          {p : Alt × Alt // beats p.1 p.2}) x y rfl rfl h1 h2
    have hmem : (⟨(a, b), hab⟩ : {p : Alt × Alt // beats p.1 p.2}) ∉ Finset.univ →
        (∑ flag : Bool,
          (if (mcgProfile beats ((⟨(a, b), hab⟩ :
            {p : Alt × Alt // beats p.1 p.2}), flag)).lt a b then (1:ℤ) else -1)) = 0 :=
      fun hcon => absurd (Finset.mem_univ _) hcon
    have hsing : (∑ e : {p : Alt × Alt // beats p.1 p.2}, ∑ flag : Bool,
          (if (mcgProfile beats (e, flag)).lt a b then (1:ℤ) else -1)) =
        (∑ flag : Bool,
          (if (mcgProfile beats ((⟨(a, b), hab⟩ :
            {p : Alt × Alt // beats p.1 p.2}), flag)).lt a b then (1:ℤ) else -1)) :=
      Finset.sum_eq_single (⟨(a, b), hab⟩ : {p : Alt × Alt // beats p.1 p.2}) hzero hmem
    rw [hsing]
    exact inner_two beats hne (⟨(a, b), hab⟩ : {p : Alt × Alt // beats p.1 p.2}) rfl rfl
  · rw [ite_eq_right hab]
    by_cases hba : beats b a
    · rw [ite_eq_left hba]
      have hzero : ∀ e' ∈ (Finset.univ : Finset {p : Alt × Alt // beats p.1 p.2}),
          e' ≠ (⟨(b, a), hba⟩ : {p : Alt × Alt // beats p.1 p.2}) →
          (∑ flag : Bool,
            (if (mcgProfile beats (e', flag)).lt a b then (1:ℤ) else -1)) = 0 := by
        intro e' _ hne'
        obtain ⟨⟨x, y⟩, hxy⟩ := e'
        have h1 : (x, y) ≠ (b, a) := fun hcon => hne' (Subtype.ext hcon)
        by_cases h2 : (x, y) = (a, b)
        · exfalso
          have hxy' : beats x y := hxy
          have hxa : x = a := congrArg Prod.fst h2
          have hyb : y = b := congrArg Prod.snd h2
          rw [hxa, hyb] at hxy'
          exact hasym hba hxy'
        · exact inner_zero beats hirrefl hne (⟨(x, y), hxy⟩ :
            {p : Alt × Alt // beats p.1 p.2}) x y rfl rfl h2 h1
      have hmem : (⟨(b, a), hba⟩ : {p : Alt × Alt // beats p.1 p.2}) ∉ Finset.univ →
          (∑ flag : Bool,
            (if (mcgProfile beats ((⟨(b, a), hba⟩ :
              {p : Alt × Alt // beats p.1 p.2}), flag)).lt a b then (1:ℤ) else -1)) = 0 :=
        fun hcon => absurd (Finset.mem_univ _) hcon
      have hsing : (∑ e : {p : Alt × Alt // beats p.1 p.2}, ∑ flag : Bool,
            (if (mcgProfile beats (e, flag)).lt a b then (1:ℤ) else -1)) =
          (∑ flag : Bool,
            (if (mcgProfile beats ((⟨(b, a), hba⟩ :
              {p : Alt × Alt // beats p.1 p.2}), flag)).lt a b then (1:ℤ) else -1)) :=
        Finset.sum_eq_single (⟨(b, a), hba⟩ : {p : Alt × Alt // beats p.1 p.2}) hzero hmem
      rw [hsing]
      exact inner_neg_two beats hne (⟨(b, a), hba⟩ :
        {p : Alt × Alt // beats p.1 p.2}) rfl rfl
    · rw [ite_eq_right hba]
      have hzero : ∀ e' ∈ (Finset.univ : Finset {p : Alt × Alt // beats p.1 p.2}),
          (∑ flag : Bool,
            (if (mcgProfile beats (e', flag)).lt a b then (1:ℤ) else -1)) = 0 := by
        intro e' _
        obtain ⟨⟨x, y⟩, hxy⟩ := e'
        have h1 : (x, y) ≠ (a, b) := by
          intro h
          have hxy' : beats x y := hxy
          have hxa : x = a := congrArg Prod.fst h
          have hyb : y = b := congrArg Prod.snd h
          rw [hxa, hyb] at hxy'
          exact hab hxy'
        have h2 : (x, y) ≠ (b, a) := by
          intro h
          have hxy' : beats x y := hxy
          have hxb : x = b := congrArg Prod.fst h
          have hya : y = a := congrArg Prod.snd h
          rw [hxb, hya] at hxy'
          exact hba hxy'
        exact inner_zero beats hirrefl hne (⟨(x, y), hxy⟩ :
          {p : Alt × Alt // beats p.1 p.2}) x y rfl rfl h1 h2
      exact Finset.sum_eq_zero hzero

/-- The McGarvey voter type has two voters per directed edge. -/
theorem card_edgeVoters {Alt : Type*} [Fintype Alt]
    (beats : Alt → Alt → Prop) [DecidableRel beats] :
    Fintype.card ({p : Alt × Alt // beats p.1 p.2} × Bool) =
      2 * (Finset.univ.filter (fun p : Alt × Alt => beats p.1 p.2)).card := by
  rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_subtype]
  omega

end

end MathlibExt.GameTheory.SocialChoice
