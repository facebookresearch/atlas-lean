/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring

@[expose] public section



variable {X : Type*} [DecidableEq X]

/-- The version space of a finite concept class `C` after
seeing labeled examples `S`: concepts agreeing with every
label. -/
def versionSpace (C : Finset (X → Bool)) (S : List (X × Bool)) :
    Finset (X → Bool) :=
  C.filter (fun c => S.all (fun e => c e.1 = e.2))

/-- Number of concepts in the version space predicting `true`
on `x`. -/
def countTrue (C : Finset (X → Bool)) (S : List (X × Bool))
    (x : X) : ℕ :=
  ((versionSpace C S).filter (fun c => c x = true)).card

/-- The halving algorithm's prediction on `x` given examples
`S`: majority vote of the version space. -/
def halvingPredict (C : Finset (X → Bool)) (S : List (X × Bool))
    (x : X) : Bool :=
  !(2 * countTrue C S x ≤ (versionSpace C S).card)

private theorem versionSpace_append_singleton {X : Type*} [DecidableEq X]
    (C : Finset (X → Bool)) (S : List (X × Bool)) (x : X) (b : Bool) :
    versionSpace C (S ++ [(x, b)]) =
      (versionSpace C S).filter (fun c => c x = b) := by
  ext c
  simp only [versionSpace, Finset.mem_filter, List.all_eq_true,
    List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨hc, hall⟩
    refine ⟨⟨hc, fun e he => hall e (Or.inl he)⟩, ?_⟩
    exact of_decide_eq_true (hall (x, b) (Or.inr rfl))
  · rintro ⟨⟨hc, hall⟩, hxb⟩
    refine ⟨hc, fun e he => ?_⟩
    rcases he with he | rfl
    · exact hall e he
    · simpa using hxb

private theorem filter_not_true_eq_filter_false {X : Type*} [DecidableEq X]
    (V : Finset (X → Bool)) (x : X) :
    V.filter (fun c => ¬(c x = true)) =
      V.filter (fun c => c x = false) := by
  ext c
  simp only [Finset.mem_filter, Bool.not_eq_true]

private theorem card_versionSpace_append_le {X : Type*} [DecidableEq X]
    (C : Finset (X → Bool)) (S : List (X × Bool)) (x : X) (b : Bool) :
    (versionSpace C (S ++ [(x, b)])).card ≤ (versionSpace C S).card := by
  rw [versionSpace_append_singleton]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- If the halving prediction on the next example is wrong,
the version space at most halves: the concepts consistent
with the new example are the minority side. -/
theorem versionSpace_card_le_of_mistake (C : Finset (X → Bool))
    (S : List (X × Bool)) (x : X) (b : Bool)
    (hmistake : halvingPredict C S x ≠ b) :
    2 * (versionSpace C (S ++ [(x, b)])).card ≤
      (versionSpace C S).card := by
  rw [versionSpace_append_singleton]
  have hpart : countTrue C S x +
      ((versionSpace C S).filter (fun c => c x = false)).card =
      (versionSpace C S).card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := versionSpace C S) (fun c => c x = true)
    change ((versionSpace C S).filter (fun c => c x = true)).card +
      ((versionSpace C S).filter (fun c => ¬(c x = true))).card = _ at h
    rw [filter_not_true_eq_filter_false] at h
    exact h
  cases b
  · simp only [halvingPredict] at hmistake
    by_cases hle : 2 * countTrue C S x ≤ (versionSpace C S).card
    · simp [hle] at hmistake
    · unfold countTrue at hpart hle
      omega
  · simp only [halvingPredict] at hmistake
    by_cases hle : 2 * countTrue C S x ≤ (versionSpace C S).card
    · unfold countTrue at hle
      exact hle
    · simp [hle] at hmistake

/-- Mistakes made by halving along a sequence, processed in
order: `seen` is the list of examples already processed. -/
def halvingMistakes (C : Finset (X → Bool)) :
    List (X × Bool) → List (X × Bool) → ℕ
  | _, [] => 0
  | seen, (x, b) :: rest =>
      (if halvingPredict C seen x = b then 0 else 1) +
        halvingMistakes C (seen ++ [(x, b)]) rest

private theorem halving_aux {X : Type*} [DecidableEq X]
    (C : Finset (X → Bool)) (c₀ : X → Bool) (_hc₀ : c₀ ∈ C)
    (seen rest : List (X × Bool))
    (hseen : ∀ e ∈ seen, c₀ e.1 = e.2)
    (hrest : ∀ e ∈ rest, c₀ e.1 = e.2) :
    2 ^ halvingMistakes C seen rest * (versionSpace C (seen ++ rest)).card ≤
      (versionSpace C seen).card := by
  induction rest generalizing seen with
  | nil =>
      simp only [halvingMistakes, pow_zero, one_mul, List.append_nil,
        le_refl]
  | cons hd tl ih =>
      obtain ⟨x, b⟩ := hd
      have hxb : c₀ x = b := hrest (x, b) (by simp)
      have hseen' : ∀ e ∈ seen ++ [(x, b)], c₀ e.1 = e.2 := by
        intro e he
        rw [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact hseen e he
        · exact hxb
      have hrest' : ∀ e ∈ tl, c₀ e.1 = e.2 := by
        intro e he
        exact hrest e (List.mem_cons_of_mem _ he)
      have happ : seen ++ (x, b) :: tl = (seen ++ [(x, b)]) ++ tl := by simp
      have ih' := ih (seen ++ [(x, b)]) hseen' hrest'
      simp only [halvingMistakes]
      by_cases hcorr : halvingPredict C seen x = b
      · rw [ite_eq_left hcorr, zero_add, happ]
        exact le_trans ih' (card_versionSpace_append_le C seen x b)
      · rw [ite_eq_right hcorr, happ, pow_add, pow_one]
        have hhalve := versionSpace_card_le_of_mistake C seen x b hcorr
        calc 2 * 2 ^ halvingMistakes C (seen ++ [(x, b)]) tl *
              (versionSpace C ((seen ++ [(x, b)]) ++ tl)).card
            = 2 * (2 ^ halvingMistakes C (seen ++ [(x, b)]) tl *
              (versionSpace C ((seen ++ [(x, b)]) ++ tl)).card) := by ring
          _ ≤ 2 * (versionSpace C (seen ++ [(x, b)])).card :=
              Nat.mul_le_mul_left 2 ih'
          _ ≤ (versionSpace C seen).card := hhalve

/-- Halving mistake bound: on any realizable sequence (some
concept in `C` labels every example), the number `m` of
halving mistakes satisfies `2 ^ m ≤ C.card`; in particular
`m ≤ Nat.log 2 C.card`. -/
theorem halving_mistakes_bound (C : Finset (X → Bool))
    (S : List (X × Bool))
    (hreal : ∃ c ∈ C, ∀ e ∈ S, c e.1 = e.2) :
    2 ^ halvingMistakes C [] S ≤ C.card := by
  obtain ⟨c₀, hc₀, hcon⟩ := hreal
  have hnil : versionSpace C [] = C := by
    ext c
    simp [versionSpace]
  have hmem : c₀ ∈ versionSpace C S := by
    simp only [versionSpace, Finset.mem_filter]
    refine ⟨hc₀, ?_⟩
    rw [List.all_eq_true]
    intro e he
    simp [hcon e he]
  have hmain := halving_aux C c₀ hc₀ [] S (by simp) hcon
  rw [List.nil_append, hnil] at hmain
  have hpos : 1 ≤ (versionSpace C S).card := Finset.card_pos.mpr ⟨c₀, hmem⟩
  calc 2 ^ halvingMistakes C [] S
      = 2 ^ halvingMistakes C [] S * 1 := (mul_one _).symm
    _ ≤ 2 ^ halvingMistakes C [] S * (versionSpace C S).card :=
        Nat.mul_le_mul_left _ hpos
    _ ≤ C.card := hmain
