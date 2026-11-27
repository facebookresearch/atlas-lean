/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import MathlibExt.GameTheory.PenultsOfTak.FifthBound
public import MathlibExt.GameTheory.PenultsOfTak.LargestPenult
public import MathlibExt.GameTheory.PenultsOfTak.WeightedCrossBound

/-!
# The second player wins Impartial Tak on even boards

A reflection strategy across a center line proves that the empty even board is a losing position.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda,
*The Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 2.
-/

namespace MetaMathlibExt

@[expose] public section

private abbrev Cell (n : ℕ) := Fin n × Fin n

private abbrev Walk {n : ℕ} (S : Finset (Cell n)) :=
  Relation.ReflTransGen (fun x y => takAdjacent x y ∧ y ∈ S)

private def mirror {n : ℕ} (p : Cell n) : Cell n := (p.1, p.2.rev)

private theorem mirror_mirror {n : ℕ} (p : Cell n) : mirror (mirror p) = p := by
  simp [mirror]

private theorem mirror_ne {n : ℕ} (hn : Even n) (p : Cell n) : mirror p ≠ p := by
  obtain ⟨k, hk⟩ := hn
  intro h
  have he := congrArg (fun x => x.2.val) h
  have hp := p.2.isLt
  simp only [mirror, Fin.val_rev] at he
  omega

private theorem adjacent_symm {n : ℕ} {x y : Cell n} (h : takAdjacent x y) :
    takAdjacent y x := by
  unfold takAdjacent at *
  tauto

private theorem adjacent_mirror {n : ℕ} {x y : Cell n} (h : takAdjacent x y) :
    takAdjacent (mirror x) (mirror y) := by
  rcases h with ⟨hr, hc⟩ | ⟨hc, hr⟩
  · refine Or.inl ⟨hr, ?_⟩
    have hx := x.2.isLt
    have hy := y.2.isLt
    simp only [mirror, Fin.val_rev]
    omega
  · exact Or.inr ⟨congrArg Fin.rev hc, hr⟩

private theorem walk_mem {n : ℕ} {S : Finset (Cell n)} {a b : Cell n}
    (ha : a ∈ S) (w : Walk S a b) : b ∈ S := by
  induction w with
  | refl => exact ha
  | tail _ h _ => exact h.2

private theorem walk_reverse {n : ℕ} {S : Finset (Cell n)} {a b : Cell n}
    (ha : a ∈ S) (w : Walk S a b) : Walk S b a := by
  induction w with
  | refl => exact .refl
  | @tail x y prev step ih =>
    exact ih.head ⟨adjacent_symm step.1, walk_mem ha prev⟩

private theorem walk_mirror {n : ℕ} {S T : Finset (Cell n)} {a b : Cell n}
    (h : ∀ x ∈ S, mirror x ∈ T) (w : Walk S a b) :
    Walk T (mirror a) (mirror b) :=
  w.lift mirror fun _ y step => ⟨adjacent_mirror step.1, h y step.2⟩

private theorem no_horizontal_left {n k : ℕ} (hn : n = k + k)
    {S : Finset (Cell n)} (hsym : ∀ x ∈ S, mirror x ∈ S) (hS : ¬ takHasRoad S)
    (p : Cell n) (hp : p.2.val < k) {a b : Cell n} (ha : a ∈ insert p S)
    (w : Walk (insert p S) a b) (har : a.2.val + 1 = n) (hbl : b.2.val = 0) : False := by
  have haS : a ∈ S := by
    rcases Finset.mem_insert.mp ha with h | h
    · subst a
      have := p.2.isLt
      omega
    · exact h
  have side {z : Cell n} (v : Walk (insert p S) a z) :
      k ≤ z.2.val ∧ Walk S a z := by
    induction v with
    | refl => exact ⟨by omega, .refl⟩
    | @tail x y prev step ih =>
      obtain ⟨hx, path⟩ := ih
      by_cases hy : k ≤ y.2.val
      · have hyS : y ∈ S := by
          rcases Finset.mem_insert.mp step.2 with h | h
          · subst y
            omega
          · exact h
        exact ⟨hy, path.tail ⟨step.1, hyS⟩⟩
      · have he : y = mirror x := by
          obtain ⟨hr, hc⟩ | ⟨hc, hr⟩ := step.1
          · refine Prod.ext (by exact hr.symm) ?_
            apply Fin.ext
            have hxlt := x.2.isLt
            have hylt := y.2.isLt
            simp only [mirror, Fin.val_rev]
            omega
          · have := congrArg Fin.val hc
            omega
        have hxS := walk_mem haS path
        have mirrored := walk_mirror hsym path
        have full := (path.tail ⟨he ▸ step.1, hsym x hxS⟩).trans
          (walk_reverse (hsym a haS) mirrored)
        have left : (mirror a).2.val = 0 := by
          simp only [mirror, Fin.val_rev]
          omega
        exact (hS ⟨mirror a, hsym a haS, a,
          walk_reverse haS full, Or.inl ⟨left, har⟩⟩).elim
  have := (side w).1
  have := a.2.isLt
  omega

private theorem no_horizontal_insert {n : ℕ} (hn : Even n)
    {S : Finset (Cell n)} (hsym : ∀ x ∈ S, mirror x ∈ S) (hS : ¬ takHasRoad S)
    (p : Cell n) {a b : Cell n} (ha : a ∈ insert p S)
    (w : Walk (insert p S) a b) (hal : a.2.val = 0) (hbr : b.2.val + 1 = n) : False := by
  obtain ⟨k, hk⟩ := hn
  by_cases hp : p.2.val < k
  · exact no_horizontal_left hk hsym hS p hp (walk_mem ha w) (walk_reverse ha w) hbr hal
  · have hp' : (mirror p).2.val < k := by
      have := p.2.isLt
      simp only [mirror, Fin.val_rev]
      omega
    have hm : ∀ x ∈ insert p S, mirror x ∈ insert (mirror p) S := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_insert_self ..
      · exact Finset.mem_insert_of_mem (hsym x hx)
    apply no_horizontal_left hk hsym hS (mirror p) hp' (hm a ha) (walk_mirror hm w)
    · simp only [mirror, Fin.val_rev]
      omega
    · simp only [mirror, Fin.val_rev]
      omega

private def fold {n : ℕ} (k : ℕ) (p x : Cell n) : Cell n :=
  if (x.2.val < k ↔ p.2.val < k) then x else mirror x

private theorem fold_self {n : ℕ} (k : ℕ) (p : Cell n) : fold k p p = p := by
  simp [fold]

private theorem fold_mirror {n k : ℕ} (hn : n = k + k) (p x : Cell n) :
    fold k p (mirror x) = fold k p x := by
  have hx := x.2.isLt
  simp only [fold, mirror_mirror]
  have hr : (mirror x).2.val = n - (x.2.val + 1) := Fin.val_rev _
  split_ifs <;> simp_all <;> omega

private theorem fold_adjacent {n k : ℕ} (hn : n = k + k) (p : Cell n)
    {x y : Cell n} (h : takAdjacent x y) :
    fold k p x = fold k p y ∨ takAdjacent (fold k p x) (fold k p y) := by
  by_cases hx : x.2.val < k ↔ p.2.val < k
  · by_cases hy : y.2.val < k ↔ p.2.val < k
    · exact Or.inr (by simpa only [fold, ite_eq_left hx, ite_eq_left hy] using h)
    · left
      simp only [fold, ite_eq_left hx, ite_eq_right hy]
      rcases h with ⟨hr, hc⟩ | ⟨hc, hr⟩
      · refine Prod.ext (by exact hr) ?_
        apply Fin.ext
        have hxlt := x.2.isLt
        have hylt := y.2.isLt
        simp only [mirror, Fin.val_rev]
        omega
      · have := congrArg Fin.val hc
        omega
  · by_cases hy : y.2.val < k ↔ p.2.val < k
    · left
      simp only [fold, ite_eq_right hx, ite_eq_left hy]
      rcases h with ⟨hr, hc⟩ | ⟨hc, hr⟩
      · refine Prod.ext (by exact hr) ?_
        apply Fin.ext
        have hxlt := x.2.isLt
        have hylt := y.2.isLt
        simp only [mirror, Fin.val_rev]
        omega
      · have := congrArg Fin.val hc
        omega
    · exact Or.inr (by simpa only [fold, ite_eq_right hx, ite_eq_right hy] using adjacent_mirror h)

private theorem vertical_after_reply {n k : ℕ} (hn : n = k + k)
    {S : Finset (Cell n)} (hsym : ∀ x ∈ S, mirror x ∈ S)
    (p q : Cell n) {a b : Cell n} (ha : a ∈ insert q (insert (mirror p) (insert p S)))
    (w : Walk (insert q (insert (mirror p) (insert p S))) a b)
    (hat : a.1.val = 0) (hbb : b.1.val + 1 = n) :
    takHasRoad (insert (fold k p q) (insert p S)) := by
  have hm : ∀ x ∈ insert q (insert (mirror p) (insert p S)),
      fold k p x ∈ insert (fold k p q) (insert p S) := by
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | rfl | rfl | hx
    · exact Finset.mem_insert_self ..
    · rw [fold_mirror hn, fold_self]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    · rw [fold_self]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      dsimp only [fold]
      split_ifs
      · exact hx
      · exact hsym x hx
  have path : Walk (insert (fold k p q) (insert p S)) (fold k p a) (fold k p b) := by
    apply w.lift' (fold k p)
    intro x y step
    change Walk (insert (fold k p q) (insert p S)) (fold k p x) (fold k p y)
    rcases fold_adjacent hn p step.1 with he | he
    · rw [he]
    · exact .single ⟨he, hm y step.2⟩
  have rows (x : Cell n) : (fold k p x).1 = x.1 := by
    dsimp only [fold]
    split_ifs <;> rfl
  exact ⟨fold k p a, hm a ha, fold k p b, path, Or.inr
    ⟨by simpa only [rows] using hat, by simpa only [rows] using hbb⟩⟩

private theorem not_win_of_road {n : ℕ} {S : Finset (Cell n)} (hS : takHasRoad S) :
    ¬ placementFirstPlayerWins takHasRoad S := by
  intro h
  exact (placementFirstPlayerWins_iff takHasRoad S).mp h |>.1 hS

private theorem safe_of_losing {n : ℕ} {S : Finset (Cell n)} (hS : ¬ takHasRoad S)
    (h : ¬ placementFirstPlayerWins takHasRoad S) (q : Cell n) :
    ¬ takHasRoad (insert q S) := by
  intro hr
  by_cases hq : q ∈ S
  · exact hS (by simpa only [Finset.insert_eq_of_mem hq] using hr)
  · exact h ((placementFirstPlayerWins_iff takHasRoad S).mpr
      ⟨hS, q, hq, not_win_of_road hr⟩)

private theorem symmetric_losing {n : ℕ} (hn : Even n) (S : Finset (Cell n))
    (hsym : ∀ x ∈ S, mirror x ∈ S) (hsafe : ∀ p, ¬ takHasRoad (insert p S)) :
    ¬ placementFirstPlayerWins takHasRoad S := by
  intro h
  obtain ⟨he, p, hp, hP⟩ := (placementFirstPlayerWins_iff takHasRoad S).mp h
  have hm : mirror p ∉ insert p S := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨mirror_ne hn p, fun hx => hp (mirror_mirror p ▸ hsym (mirror p) hx)⟩
  let T := insert (mirror p) (insert p S)
  have hT : ¬ takHasRoad T := safe_of_losing (hsafe p) hP (mirror p)
  have hsymT : ∀ x ∈ T, mirror x ∈ T := by
    intro x hx
    simp only [T, Finset.mem_insert] at hx ⊢
    rcases hx with rfl | rfl | hx
    · exact Or.inr (Or.inl (mirror_mirror p))
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (hsym x hx))
  have hsafeT (q : Cell n) : ¬ takHasRoad (insert q T) := by
    rintro ⟨a, ha, b, path, ends⟩
    rcases ends with ⟨left, right⟩ | ⟨top, bottom⟩
    · exact no_horizontal_insert hn hsymT hT q ha path left right
    · obtain ⟨k, hk⟩ := hn
      exact safe_of_losing (hsafe p) hP (fold k p q)
        (vertical_after_reply hk hsym p q ha path top bottom)
  have hlose : ¬ placementFirstPlayerWins takHasRoad T :=
    symmetric_losing hn T hsymT hsafeT
  exact hP ((placementFirstPlayerWins_iff takHasRoad (insert p S)).mpr
    ⟨hsafe p, mirror p, hm, hlose⟩)
termination_by Fintype.card (Cell n) - S.card
decreasing_by
  have hc := Finset.card_insert_of_notMem hp
  have hc' := Finset.card_insert_of_notMem hm
  have hlt := Finset.card_lt_univ_of_notMem hp
  simp only [Cell] at *
  omega

private theorem no_road_singleton {n : ℕ} (hn : Even n) (p : Cell n) :
    ¬ takHasRoad (insert p ∅) := by
  rintro ⟨a, ha, b, path, ends⟩
  have ha' : a = p := by simpa using ha
  have hb' : b = p := by simpa using walk_mem ha path
  subst a b
  obtain ⟨k, hk⟩ := hn
  rcases ends with ⟨left, right⟩ | ⟨top, bottom⟩ <;> omega

/-- **The second player wins Impartial Tak on even boards.** Impartial Tak is the impartial
placement game on the $n \times n$ board in which the players alternately place a token on an
empty cell, play ends once the tokens contain a road, and the player unable to move loses. If $n$
is even, the first player does not win from the empty $n \times n$ board, that is, the second
player wins.

Source: Boris Alexeev, Paul Ellis, Michael Richter, and Thotsaporn Aek Thanatipanonda, *The
Penults of Tak: Adventures in Impartial, Normal-Play, Positional Games*, INTEGERS 25 (2025),
Article G1, Proposition 2 (`integers-2025-G1-prop-2`). -/
public theorem impartialTak_not_firstPlayerWins_of_even {n : ℕ} (hn : Even n) :
    ¬ placementFirstPlayerWins takHasRoad (∅ : Finset (Fin n × Fin n))
    := by
  exact symmetric_losing hn ∅ (by simp) (no_road_singleton hn)

end

end MetaMathlibExt
