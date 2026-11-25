/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.ReflectionCalculus
public import Mathlib.SetTheory.Ordinal.Veblen

/-!
# Ordinal assignment for worms in the Reflection Calculus

The ordinal assignment uses the sequent calculus and worms from
`CSLibExt.Logics.Modal.ReflectionCalculus`. The main result, `Cslib.Modal.RC.exists_wormOrdinal`,
gives a map `o` from worms to ordinals such that two worms are RC-equivalent iff they have the same
value, `α <₀ β` iff `o α < o β`, and the values are exactly the ordinals below `ε₀`.

## Proof outline

* The map is the ordinal calculation `o(⊤) = 0` and `o(h 0 r) = o(r) + ω ^ o(h⁻)` for a worm `h`
  without the letter `0`, where `h⁻` lowers every letter by one and a nonempty worm `h` without
  `0` counts as `h 0 ⊤`. Unfolding it along the blocks of `α = α₁ 0 α₂ 0 ⋯ 0 αₙ` gives
  `o(α) = ω ^ o(αₙ⁻) + ⋯ + ω ^ o(α₁⁻)`, without the term of `αₙ` when `αₙ` is empty.
* A nonempty worm `h 0 r` (or `h`, with `r = ⊤`) is RC-equivalent to `h ∧ ⟨0⟩r`, by axioms 4
  to 6, and raising every modality by one preserves derivability. A strong induction on the
  lengths and letter sums of two worms `α`, `β` then shows that `o α < o β` implies `β ⊢ ⟨0⟩α`
  and that `o α = o β` implies `β ⊢ α`. Its ordinal step is that `a + ω ^ x < b + ω ^ y` forces
  `a + ω ^ x ≤ b` or `x < y`.
* No worm proves its own consistency: `α ⊬ ⟨0⟩α`, by soundness (`Derives.sound`) in a finite
  RC-model on the positions `0, …, |α|` of `α`. From position `i`, the relation `R n` reaches each
  later position `j` such that the letters read from `i` to `j` are at least `n`, and each
  position `1 ≤ j ≤ i` such that the letters read from `j - 1` to `i` exceed `n`. Position `0`
  satisfies `α`, but from a position `p > t` the letter at index `t` of `α` (counting from `0`)
  only leads to positions `q > t + 1`, so no other position satisfies `α`.
* Irreflexivity and the two implications give both equivalences. The values lie below `ε₀`
  because `ε₀ = ω ^ ε₀` is closed under addition and under `ω ^ ·`, and each `ξ < ε₀` is a value:
  write `ξ = ζ + ω ^ e` with `ζ, e < ξ`.
-/

namespace Cslib.Modal.RC

namespace WormOrdinal

open Ordinal

universe u

variable {Atom : Type u}

/-! ### Derivations between worms -/

private theorem dia_zero (n : ℕ) (A : Formula Atom) : Derives (.dia n A) (.dia 0 A) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact .refl _
  · exact .monotone hn A

private theorem worm_cons_dia_zero_top (n : ℕ) (l : List ℕ) :
    Derives (worm (n :: l) : Formula Atom) (.dia 0 .top) :=
  (Derives.dia_mono n (.top _)).trans (dia_zero n _)

private theorem dia_and_dia_zero (m : ℕ) (A B : Formula Atom) :
    Derives (.dia m (.and A (.dia 0 B))) (.and (.dia m A) (.dia 0 B)) :=
  .and_intro (.dia_mono m (.and_left _ _))
    ((Derives.dia_mono m (.and_right _ _)).trans (.dia_dia_of_le (Nat.zero_le m) B))

/-- Raise every modality by one. -/
private def shift : Formula Atom → Formula Atom
  | .atom p => .atom p
  | .top => .top
  | .and A B => .and (shift A) (shift B)
  | .dia n A => .dia (n + 1) (shift A)

private theorem derives_shift {A B : Formula Atom} (h : Derives A B) :
    Derives (shift A) (shift B) := by
  induction h with
  | refl => exact .refl _
  | top => exact .top _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | and_left => exact .and_left _ _
  | and_right => exact .and_right _ _
  | and_intro _ _ ih₁ ih₂ => exact .and_intro ih₁ ih₂
  | dia_mono n _ ih => exact .dia_mono (n + 1) ih
  | dia_dia n A => exact .dia_dia (n + 1) _
  | dia_dia_of_le h A => exact .dia_dia_of_le (Nat.succ_le_succ h) _
  | dia_dia_of_le' h A => exact .dia_dia_of_le' (Nat.succ_le_succ h) _
  | dia_and h A B => exact .dia_and (Nat.succ_lt_succ h) _ _
  | monotone h A => exact .monotone (Nat.succ_lt_succ h) _

private theorem worm_map_succ (l : List ℕ) :
    (worm (l.map (· + 1)) : Formula Atom) = shift (worm l) := by
  induction l with
  | nil => rfl
  | cons n l ih => exact congrArg (Formula.dia (n + 1)) ih

/-! ### Splitting a worm at its first `0` -/

/-- Split a worm at its first `0`: the part before it, lowered by one, and the part after it. -/
private def splitZero : List ℕ → List ℕ × List ℕ
  | [] => ([], [])
  | 0 :: r => ([], r)
  | (n + 1) :: l => (n :: (splitZero l).1, (splitZero l).2)

/-- The length plus the letter sum of a worm, which decreases along the recursion of `wormOrd`. -/
private def wormSize (l : List ℕ) : ℕ := l.length + l.sum

private theorem splitZero_size_le : ∀ l : List ℕ,
    wormSize (splitZero l).1 + wormSize (splitZero l).2 ≤ wormSize l
  | [] => by simp [splitZero, wormSize]
  | 0 :: r => by simp [splitZero, wormSize]
  | (n + 1) :: l => by
    have := splitZero_size_le l
    simp only [splitZero, wormSize, List.length_cons, List.sum_cons] at this ⊢
    omega

private theorem splitZero_size_lt : ∀ {l : List ℕ}, l ≠ [] →
    wormSize (splitZero l).1 + wormSize (splitZero l).2 < wormSize l
  | 0 :: r, _ => by simp [splitZero, wormSize]
  | (n + 1) :: l, _ => by
    have := splitZero_size_le l
    simp only [splitZero, wormSize, List.length_cons, List.sum_cons] at this ⊢
    omega

private theorem splitZero_map_succ_append (g r : List ℕ) :
    splitZero (g.map (· + 1) ++ 0 :: r) = (g, r) := by
  induction g with
  | nil => rfl
  | cons n g ih => simp [splitZero, ih]

/-- A nonempty worm `h 0 r`, or `h` without the letter `0`, is RC-equivalent to `h ∧ ⟨0⟩r`
(with `r = ⊤` in the second case). -/
private theorem worm_split : ∀ {l : List ℕ}, l ≠ [] →
    Derives (worm l : Formula Atom)
        (.and (worm ((splitZero l).1.map (· + 1))) (.dia 0 (worm (splitZero l).2))) ∧
      Derives (.and (worm ((splitZero l).1.map (· + 1))) (.dia 0 (worm (splitZero l).2)))
        (worm l : Formula Atom)
  | 0 :: r, _ => ⟨.and_intro (.top _) (.refl _), .and_right _ _⟩
  | [n + 1], _ => ⟨.and_intro (.refl _) (worm_cons_dia_zero_top _ _), .and_left _ _⟩
  | (n + 1) :: m :: l, _ => by
    obtain ⟨h₁, h₂⟩ := worm_split (List.cons_ne_nil m l)
    exact ⟨(Derives.dia_mono (n + 1) h₁).trans (dia_and_dia_zero _ _ _),
      (Derives.dia_and (Nat.succ_pos n) _ _).trans (.dia_mono (n + 1) h₂)⟩

/-! ### The ordinal of a worm -/

/-- The ordinal of a worm: `o(⊤) = 0` and `o(h 0 r) = o(r) + ω ^ o(h⁻)` for a worm `h` without the
letter `0`, where a nonempty worm `h` without `0` counts as `h 0 ⊤`. -/
private noncomputable def wormOrd : List ℕ → Ordinal.{0}
  | [] => 0
  | a :: l => wormOrd (splitZero (a :: l)).2 + ω ^ wormOrd (splitZero (a :: l)).1
termination_by l => wormSize l
decreasing_by
  all_goals
    have := splitZero_size_lt (List.cons_ne_nil a l)
    omega

private theorem wormOrd_eq {l : List ℕ} (hl : l ≠ []) :
    wormOrd l = wormOrd (splitZero l).2 + ω ^ wormOrd (splitZero l).1 := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hl
  rw [wormOrd]

private theorem wormOrd_nil : wormOrd [] = 0 := by
  rw [wormOrd]

private theorem wormOrd_pos {l : List ℕ} (hl : l ≠ []) : 0 < wormOrd l := by
  rw [wormOrd_eq hl]
  exact lt_of_lt_of_le (opow_pos _ omega0_pos) (le_add_left le_rfl)

/-! ### Ordinal arithmetic -/

private theorem add_opow_lt_add_opow {a b x y : Ordinal} (ha : a < b + ω ^ y) (hxy : x < y) :
    a + ω ^ x < b + ω ^ y := by
  have hxy' : ω ^ x < ω ^ y := (opow_lt_opow_iff_right one_lt_omega0).2 hxy
  rcases lt_or_ge a b with hab | hba
  · exact (add_le_add_left hab.le _).trans_lt (add_lt_add_right hxy' _)
  · obtain ⟨δ, rfl⟩ : ∃ δ, a = b + δ := ⟨a - b, (Ordinal.add_sub_cancel_of_le hba).symm⟩
    rw [add_assoc]
    exact add_lt_add_right (isPrincipal_add_omega0_opow y ((add_lt_add_iff_left b).1 ha) hxy') _

/-- If `a + ω ^ x < b + ω ^ y`, then either `a + ω ^ x ≤ b` or the last exponents satisfy
`x < y`. -/
private theorem le_or_lt_of_add_opow_lt {a b x y : Ordinal} (h : a + ω ^ x < b + ω ^ y) :
    a + ω ^ x ≤ b ∨ x < y := by
  refine or_iff_not_imp_left.2 fun hb ↦ lt_of_not_ge fun hyx ↦ h.not_ge ?_
  have hyx' : ω ^ y ≤ ω ^ x := (opow_le_opow_iff_right one_lt_omega0).2 hyx
  rcases lt_or_ge b a with hba | hab
  · exact (add_le_add_left hba.le _).trans (add_le_add_right hyx' _)
  · obtain ⟨δ, rfl⟩ : ∃ δ, b = a + δ := ⟨b - a, (Ordinal.add_sub_cancel_of_le hab).symm⟩
    rw [add_assoc]
    refine add_le_add_right ((add_le_add_right hyx' _).trans_eq (add_omega0_opow ?_)) _
    exact (add_lt_add_iff_left a).1 (lt_of_not_ge hb)

private theorem eq_of_add_opow_eq {a b x y : Ordinal} (h : a + ω ^ x = b + ω ^ y) : x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exact absurd h (add_opow_lt_add_opow
      (h ▸ lt_add_of_pos_right a (opow_pos x omega0_pos)) hxy).ne
  · exact hxy
  · exact absurd h.symm (add_opow_lt_add_opow
      (h.symm ▸ lt_add_of_pos_right b (opow_pos y omega0_pos)) hxy).ne

/-! ### Comparing worms by their ordinals -/

/-- Comparing ordinals gives derivations: `o A < o B` implies `B ⊢ ⟨0⟩A`, and `o A = o B` implies
`B ⊢ A`, by strong induction on `wormSize A + wormSize B`. -/
private theorem derives_of_wormOrd_aux : ∀ N : ℕ, ∀ A B : List ℕ, wormSize A + wormSize B < N →
    (wormOrd A < wormOrd B → Derives (worm B : Formula Atom) (.dia 0 (worm A))) ∧
      (wormOrd A = wormOrd B → Derives (worm B : Formula Atom) (worm A))
  | 0 => fun _ _ h ↦ absurd h (Nat.not_lt_zero _)
  | N + 1 => fun A B hN ↦ by
    have ih := derives_of_wormOrd_aux N
    constructor
    · intro hlt
      rcases eq_or_ne B [] with rfl | hB
      · exact absurd hlt (by simp [wormOrd_nil])
      rcases eq_or_ne A [] with rfl | hA
      · obtain ⟨b, B, rfl⟩ := List.exists_cons_of_ne_nil hB
        exact worm_cons_dia_zero_top b B
      have hsA := splitZero_size_lt hA
      have hsB := splitZero_size_lt hB
      obtain ⟨-, hA₂⟩ := worm_split (Atom := Atom) hA
      obtain ⟨hB₁, -⟩ := worm_split (Atom := Atom) hB
      have hlt' := hlt
      rw [wormOrd_eq hA, wormOrd_eq hB] at hlt'
      rcases le_or_lt_of_add_opow_lt hlt' with h | h
      · rw [← wormOrd_eq hA] at h
        have hBr := hB₁.trans (.and_right _ _)
        rcases h.lt_or_eq with h' | h'
        · exact hBr.trans ((Derives.dia_mono 0 ((ih A _ (by omega)).1 h')).trans (.dia_dia 0 _))
        · exact hBr.trans (.dia_mono 0 ((ih A _ (by omega)).2 h'))
      · have h₁ := derives_shift ((ih _ _ (by omega)).1 h)
        rw [← worm_map_succ, shift, ← worm_map_succ] at h₁
        have hrA : wormOrd (splitZero A).2 < wormOrd B := by
          refine lt_of_le_of_lt ?_ hlt
          rw [wormOrd_eq hA]
          exact le_self_add
        have h₂ := (ih _ _ (by omega)).1 hrA
        exact (Derives.and_intro (hB₁.trans ((Derives.and_left _ _).trans h₁)) h₂).trans
          ((Derives.dia_and Nat.one_pos _ _).trans
            ((Derives.dia_mono 1 hA₂).trans (.monotone Nat.one_pos _)))
    · intro heq
      rcases eq_or_ne A [] with rfl | hA
      · exact .top _
      rcases eq_or_ne B [] with rfl | hB
      · exact absurd (heq.trans wormOrd_nil) (wormOrd_pos hA).ne'
      have hsA := splitZero_size_lt hA
      have hsB := splitZero_size_lt hB
      obtain ⟨-, hA₂⟩ := worm_split (Atom := Atom) hA
      obtain ⟨hB₁, -⟩ := worm_split (Atom := Atom) hB
      have heq' := heq
      rw [wormOrd_eq hA, wormOrd_eq hB] at heq'
      have h₁ := derives_shift ((ih _ _ (by omega)).2 (eq_of_add_opow_eq heq'))
      rw [← worm_map_succ, ← worm_map_succ] at h₁
      have hrA : wormOrd (splitZero A).2 < wormOrd B := by
        rw [← heq, wormOrd_eq hA]
        exact lt_add_of_pos_right _ (opow_pos _ omega0_pos)
      have h₂ := (ih _ _ (by omega)).1 hrA
      exact (Derives.and_intro (hB₁.trans ((Derives.and_left _ _).trans h₁)) h₂).trans hA₂

private theorem derives_dia_of_wormOrd_lt {A B : List ℕ} (h : wormOrd A < wormOrd B) :
    Derives (worm B : Formula Atom) (.dia 0 (worm A)) :=
  (derives_of_wormOrd_aux _ A B (Nat.lt_succ_self _)).1 h

private theorem derives_of_wormOrd_eq {A B : List ℕ} (h : wormOrd A = wormOrd B) :
    Derives (worm B : Formula Atom) (worm A) :=
  (derives_of_wormOrd_aux _ A B (Nat.lt_succ_self _)).2 h

/-! ### Irreflexivity of `<₀` -/

/-- The accessibility relations of a countermodel for `α ⊢ ⟨0⟩α`. Only the positions `0, …, |α|`
of `α` are related: from `i`, the relation `R n` reaches every later position `j` such that the
letters of `α` at indices `i, …, j - 1` are at least `n`, and every position `1 ≤ j ≤ i` such that
the letters at indices `j - 1, …, i - 1` are greater than `n`. -/
private def wormRel (α : List ℕ) (n i j : ℕ) : Prop :=
  (i < j ∧ j ≤ α.length ∧ ∀ s, i ≤ s → s < j → n ≤ α.getD s 0) ∨
    (0 < j ∧ j ≤ i ∧ i ≤ α.length ∧ ∀ s, j - 1 ≤ s → s < i → n < α.getD s 0)

private theorem wormRel_isFrame (α : List ℕ) : IsFrame (wormRel α) where
  polytrans := by
    rintro m n x y z (⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩) (⟨h5, h6, h7⟩ | ⟨h5, h6, h7, h8⟩)
    · refine .inl ⟨by omega, h6, fun s hs1 hs2 ↦ ?_⟩
      rcases lt_or_ge s y with hs | hs
      · exact (min_le_left _ _).trans (h3 s hs1 hs)
      · exact (min_le_right _ _).trans (h7 s hs hs2)
    · rcases lt_or_ge x z with hxz | hzx
      · exact .inl ⟨hxz, by omega, fun s hs1 hs2 ↦ (min_le_left _ _).trans (h3 s hs1 (by omega))⟩
      · exact .inr ⟨h5, hzx, by omega, fun s hs1 hs2 ↦
          (min_le_right _ _).trans_lt (h8 s hs1 (by omega))⟩
    · rcases lt_or_ge x z with hxz | hzx
      · exact .inl ⟨hxz, h6, fun s hs1 hs2 ↦ (min_le_right _ _).trans (h7 s (by omega) hs2)⟩
      · exact .inr ⟨by omega, hzx, h3, fun s hs1 hs2 ↦
          (min_le_left _ _).trans_lt (h4 s (by omega) hs2)⟩
    · refine .inr ⟨h5, by omega, h3, fun s hs1 hs2 ↦ ?_⟩
      rcases lt_or_ge s y with hs | hs
      · exact (min_le_right _ _).trans_lt (h8 s hs1 hs)
      · exact (min_le_left _ _).trans_lt (h4 s (by omega) hs2)
  condJ := by
    rintro m n x y z hnm (⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩) (⟨h5, h6, h7⟩ | ⟨h5, h6, h7, h8⟩)
    · rcases lt_or_ge y z with hyz | hzy
      · exact .inl ⟨hyz, h6, fun s hs1 hs2 ↦ h7 s (by omega) hs2⟩
      · exact .inr ⟨by omega, hzy, h2, fun s hs1 hs2 ↦ hnm.trans_le (h3 s (by omega) hs2)⟩
    · refine .inr ⟨h5, by omega, h2, fun s hs1 hs2 ↦ ?_⟩
      rcases lt_or_ge s x with hs | hs
      · exact h8 s hs1 hs
      · exact hnm.trans_le (h3 s hs hs2)
    · refine .inl ⟨by omega, h6, fun s hs1 hs2 ↦ ?_⟩
      rcases lt_or_ge s x with hs | hs
      · exact (hnm.trans (h4 s (by omega) hs)).le
      · exact h7 s hs hs2
    · rcases lt_or_ge y z with hyz | hzy
      · exact .inl ⟨hyz, by omega, fun s hs1 hs2 ↦ (hnm.trans (h4 s (by omega) (by omega))).le⟩
      · exact .inr ⟨h5, hzy, by omega, fun s hs1 hs2 ↦ h8 s hs1 (by omega)⟩
  monotone := by
    rintro m n x y hnm (⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩)
    · exact .inl ⟨h1, h2, fun s hs1 hs2 ↦ hnm.le.trans (h3 s hs1 hs2)⟩
    · exact .inr ⟨h1, h2, h3, fun s hs1 hs2 ↦ hnm.trans (h4 s hs1 hs2)⟩

/-- Position `i` of the countermodel satisfies the suffix of `α` from `i`. -/
private theorem satisfies_worm_drop (α : List ℕ) (V : ℕ → Atom → Prop) :
    ∀ d i, i + d = α.length → Satisfies (wormRel α) V i (worm (α.drop i))
  | 0, i, h => by
    rw [List.drop_eq_nil_of_le (by omega)]
    trivial
  | d + 1, i, h => by
    have hi : i < α.length := by omega
    rw [List.drop_eq_getElem_cons hi]
    refine ⟨i + 1, .inl ⟨by omega, by omega, fun s hs1 hs2 ↦ ?_⟩,
      satisfies_worm_drop α V d (i + 1) (by omega)⟩
    simp [show s = i by omega, List.getD_eq_getElem?_getD, hi]

/-- A position beyond `t` does not satisfy the suffix of `α` from `t`: following the letters of
that suffix never brings the position back to the letter being read. -/
private theorem not_satisfies_worm_drop (α : List ℕ) (V : ℕ → Atom → Prop) :
    ∀ d t p, t + d = α.length → t < p → p ≤ α.length →
      ¬Satisfies (wormRel α) V p (worm (α.drop t))
  | 0, t, p, h, htp, hp => by omega
  | d + 1, t, p, h, htp, hp => by
    have ht : t < α.length := by omega
    rw [List.drop_eq_getElem_cons ht]
    rintro ⟨q, hq, hsat⟩
    refine not_satisfies_worm_drop α V d (t + 1) q (by omega) ?_ ?_ hsat
    · rcases hq with ⟨h1, -, -⟩ | ⟨-, h2, -, h4⟩
      · omega
      · by_contra hqt
        have := h4 t (by omega) htp
        simp [List.getD_eq_getElem?_getD, ht] at this
    · rcases hq with ⟨-, h2, -⟩ | ⟨-, h2, h3, -⟩ <;> omega

/-- **Irreflexivity of `<₀`.** No worm proves its own consistency. -/
private theorem not_wormLt_self (α : List ℕ) : ¬WormLt (Atom := Atom) α α := by
  intro h
  have h₀ := satisfies_worm_drop (Atom := Atom) α (fun _ _ ↦ True) α.length 0
    (Nat.zero_add _)
  rw [List.drop_zero] at h₀
  obtain ⟨q, hq, hsat⟩ := Derives.sound (wormRel_isFrame α) (fun _ _ ↦ True) h 0 h₀
  rcases hq with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
  · exact not_satisfies_worm_drop α _ α.length 0 q (Nat.zero_add _) h1 h2
      (by rwa [List.drop_zero])
  · omega

/-! ### The ordinals of worms are the ordinals below `ε₀` -/

private theorem wormOrd_lt_epsilon_aux : ∀ N : ℕ, ∀ l : List ℕ, wormSize l < N → wormOrd l < ε₀
  | 0 => fun _ h ↦ absurd h (Nat.not_lt_zero _)
  | N + 1 => fun l hN ↦ by
    rcases eq_or_ne l [] with rfl | hl
    · rw [wormOrd_nil]
      exact epsilon_pos 0
    have hs := splitZero_size_lt hl
    have h₁ := wormOrd_lt_epsilon_aux N _ (show wormSize (splitZero l).1 < N by omega)
    have h₂ := wormOrd_lt_epsilon_aux N _ (show wormSize (splitZero l).2 < N by omega)
    rw [wormOrd_eq hl, ← omega0_opow_epsilon 0]
    rw [← omega0_opow_epsilon 0] at h₂
    exact isPrincipal_add_omega0_opow _ h₂ ((opow_lt_opow_iff_right one_lt_omega0).2 h₁)

private theorem wormOrd_lt_epsilon (l : List ℕ) : wormOrd l < ε₀ :=
  wormOrd_lt_epsilon_aux _ l (Nat.lt_succ_self _)

/-- Every nonzero ordinal is `ζ + ω ^ e` for some `ζ` and `e`. -/
private theorem exists_eq_add_omega0_opow :
    ∀ ξ : Ordinal.{0}, ξ ≠ 0 → ∃ ζ e : Ordinal.{0}, ξ = ζ + ω ^ e := by
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ ih =>
    intro hξ
    have h₁ : ω ^ log ω ξ ≤ ξ := opow_log_le_self ω hξ
    by_cases hρ : ξ - ω ^ log ω ξ = 0
    · exact ⟨0, log ω ξ, by rw [zero_add]; exact le_antisymm (Ordinal.sub_eq_zero_iff_le.1 hρ) h₁⟩
    · obtain ⟨ζ, e, he⟩ := ih _ (isLeast_sub_lt_omega0_opow_log hξ).1 hρ
      exact ⟨ω ^ log ω ξ + ζ, e, by rw [add_assoc, ← he, Ordinal.add_sub_cancel_of_le h₁]⟩

private theorem exists_wormOrd_eq : ∀ ξ : Ordinal.{0}, ξ < ε₀ → ∃ l, wormOrd l = ξ := by
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ ih =>
    intro hξ
    rcases eq_or_ne ξ 0 with rfl | h0
    · exact ⟨[], wormOrd_nil⟩
    obtain ⟨ζ, e, rfl⟩ := exists_eq_add_omega0_opow ξ h0
    have hpos : 0 < ω ^ e := opow_pos e omega0_pos
    have hζ : ζ < ζ + ω ^ e := lt_add_of_pos_right ζ hpos
    have he : e < ζ + ω ^ e := by
      refine lt_of_lt_of_le ?_ (le_add_left le_rfl)
      refine lt_of_not_ge fun h ↦ ?_
      have := epsilon_zero_le_of_omega0_opow_le h
      exact absurd ((this.trans (right_le_opow e one_lt_omega0)).trans (le_add_left le_rfl))
        hξ.not_ge
    obtain ⟨r, hr⟩ := ih ζ hζ (hζ.trans hξ)
    obtain ⟨g, hg⟩ := ih e he (he.trans hξ)
    refine ⟨g.map (· + 1) ++ 0 :: r, ?_⟩
    rw [wormOrd_eq (by simp), splitZero_map_succ_append, hr, hg]

end WormOrdinal

/-- **Worms have order type `ε₀`.** There is a map `o` from worms to ordinals such that two worms
are RC-equivalent iff they have the same value, `α <₀ β` iff `o α < o β`, and the values are
exactly the ordinals below `ε₀`; that is, worms modulo RC-equivalence, ordered by `<₀`, are
order-isomorphic to `ε₀`. Beklemishev states this for GLP, with `α <₀ β` iff
`GLP ⊢ β → ⟨0⟩α`, together with the fact that every closed strictly positive formula is
GLP-equivalent to a worm ("Provability algebras: an overview and current progress", slides, 2012,
on the positive closed fragment as an ordinal notation system); the result is due to
Beklemishev, "Provability algebras and proof-theoretic ordinals, I", *Annals of Pure and Applied
Logic* 128 (2004), listed in Verbrugge, "Provability logic", *Stanford Encyclopedia of
Philosophy*, §5.4 under "GLP and proof-theoretic ordinals" (that paper was not read here).
The RC form stated here
follows because RC axiomatizes the strictly positive fragment of GLP (Dashkov, as reported in
arXiv:1304.4396v3, Section 2). The proved
`WormLt.replicate_zero_one` is the instance `o(0^k) = k < ω = o(1)`. -/
public theorem exists_wormOrdinal :
    ∃ o : List ℕ → Ordinal.{0},
      (∀ α β, o α = o β ↔
        (Derives (worm α : Formula Empty) (worm β) ∧
          Derives (worm β : Formula Empty) (worm α))) ∧
      (∀ α β, WormLt (Atom := Empty) α β ↔ o α < o β) ∧
      Set.range o = Set.Iio (Ordinal.epsilon 0) := by
  refine ⟨WormOrdinal.wormOrd, fun α β ↦ ⟨fun h ↦ ⟨WormOrdinal.derives_of_wormOrd_eq h.symm,
    WormOrdinal.derives_of_wormOrd_eq h⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩,
    fun α β ↦ ⟨fun h ↦ ?_, WormOrdinal.derives_dia_of_wormOrd_lt⟩, ?_⟩
  · rcases lt_trichotomy (WormOrdinal.wormOrd α) (WormOrdinal.wormOrd β) with h | h | h
    · exact absurd (h₁.trans (WormOrdinal.derives_dia_of_wormOrd_lt h))
        (WormOrdinal.not_wormLt_self α)
    · exact h
    · exact absurd (h₂.trans (WormOrdinal.derives_dia_of_wormOrd_lt h))
        (WormOrdinal.not_wormLt_self β)
  · rcases lt_trichotomy (WormOrdinal.wormOrd α) (WormOrdinal.wormOrd β) with h' | h' | h'
    · exact h'
    · exact absurd (h.trans (.dia_mono 0 (WormOrdinal.derives_of_wormOrd_eq h'.symm)))
        (WormOrdinal.not_wormLt_self β)
    · exact absurd (h.trans ((Derives.dia_mono 0 (WormOrdinal.derives_dia_of_wormOrd_lt h')).trans
        (.dia_dia 0 _))) (WormOrdinal.not_wormLt_self β)
  · ext ξ
    exact ⟨fun ⟨l, hl⟩ ↦ hl ▸ WormOrdinal.wormOrd_lt_epsilon l, WormOrdinal.exists_wormOrd_eq ξ⟩

end Cslib.Modal.RC
