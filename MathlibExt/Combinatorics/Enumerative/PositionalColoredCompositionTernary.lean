/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.PositionalColoredCompositions
public import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Infix

/-!
# Even colored compositions and ternary strings

The number of even colored compositions of `k` equals the number of ternary strings of length
`k` that avoid `01` and `12`, begin with a letter other than `2`, and end with a letter other
than `0`, with the empty string included at `k = 0`.
-/

namespace MetaMathlibExt
namespace even_eq_ternaryStrings_avoiding

/-- Two consecutive letters in a ternary word are allowed unless they form `01` or `12`. -/
private def step (a b : Fin 3) : Prop :=
  ¬ (a = 0 ∧ b = 1) ∧ ¬ (a = 1 ∧ b = 2)

private instance stepDecidable (a b : Fin 3) : Decidable (step a b) := by
  unfold step
  infer_instance

/-- Valid suffixes of length `n` after a given preceding letter. -/
private def Words (n : ℕ) (a : Fin 3) :=
  {w : List (Fin 3) // w.length = n ∧ ¬ [0, 1] <:+: a :: w ∧ ¬ [1, 2] <:+: a :: w ∧
    (a :: w).getLast? ≠ some 0}

private theorem cons_valid (a b : Fin 3) (w : List (Fin 3)) :
    (¬ [0, 1] <:+: a :: b :: w ∧ ¬ [1, 2] <:+: a :: b :: w ∧
      (a :: b :: w).getLast? ≠ some 0) ↔
    (¬ [0, 1] <:+: b :: w ∧ ¬ [1, 2] <:+: b :: w ∧ (b :: w).getLast? ≠ some 0) ∧
      step a b := by
  rw [List.infix_cons_iff (a := a), List.infix_cons_iff (l₁ := [1, 2]) (a := a),
    List.getLast?_cons_cons]
  simp only [List.cons_prefix_cons, List.nil_prefix, and_true, not_or, eq_comm (a := a),
    eq_comm (a := b), step]
  tauto

private theorem words_finite (n : ℕ) (a : Fin 3) : Finite (Words n a) := by
  apply Finite.of_injective
    (fun w : Words n a => fun i : Fin n => w.val.get (i.cast w.property.1.symm))
  intro v w h
  apply Subtype.ext
  apply List.ext_get (v.property.1.trans w.property.1.symm)
  intro i hi _
  exact congrFun h ⟨i, v.property.1 ▸ hi⟩

/-- Split a nonempty suffix into its first letter and the suffix that follows it. -/
private def wordsSuccEquiv (n : ℕ) (a : Fin 3) :
    Words (n + 1) a ≃ Σ b : Fin 3, {_w : Words n b // step a b} where
  toFun
    | ⟨[], hl, _⟩ => by simp at hl
    | ⟨b :: w, hl, hw⟩ =>
      let h := (cons_valid a b w).mp hw
      ⟨b, ⟨⟨w, Nat.succ.inj hl, h.1⟩, h.2⟩⟩
  invFun
    | ⟨b, ⟨⟨w, hl, hw⟩, hab⟩⟩ =>
      ⟨b :: w, congrArg Nat.succ hl, (cons_valid a b w).mpr ⟨hw, hab⟩⟩
  left_inv := by
    rintro ⟨_ | ⟨b, w⟩, hl, hw⟩
    · simp at hl
    · rfl
  right_inv := by rintro ⟨b, ⟨w, hl, hw⟩, hab⟩; rfl

private theorem words_zero (a : Fin 3) :
    Nat.card (Words 0 a) = if a = 0 then 0 else 1 := by
  split_ifs with ha
  · subst a
    have : IsEmpty (Words 0 0) := ⟨fun w => by
      have hw := w.property.2.2.2
      rw [List.length_eq_zero_iff.mp w.property.1] at hw
      exact hw rfl⟩
    simp
  · apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨[], ?_⟩, fun w => Subtype.ext (List.length_eq_zero_iff.mp w.property.1)⟩
    simp [List.infix_cons_iff, List.cons_prefix_cons, ha]

private theorem words_succ (n : ℕ) (a : Fin 3) :
    Nat.card (Words (n + 1) a) =
      ∑ b : Fin 3, if step a b then Nat.card (Words n b) else 0 := by
  classical
  let (b : Fin 3) : Finite (Words n b) := words_finite n b
  rw [Nat.card_congr (wordsSuccEquiv n a), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : step a b
  · rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => h)]
    simp [h]
  · have : IsEmpty {_w : Words n b // step a b} := ⟨fun w => h w.property⟩
    simp [h]

/-- Increasing the first part preserves the remaining parts. -/
private def bump : List ℕ → List ℕ
  | [] => []
  | p :: ps => (p + 1) :: ps

/-- Increase the first part, or prepend a part of size one. -/
private def extend {n : ℕ} (hn : 1 ≤ n) :
    Composition n ⊕ Composition n → Composition (n + 1)
  | .inl ⟨[], _, hs⟩ => by simp at hs; omega
  | .inl ⟨p :: ps, hp, hs⟩ =>
    ⟨(p + 1) :: ps, by
      simpa using fun i (hi : i ∈ ps) => hp (List.mem_cons_of_mem _ hi), by
      simp only [List.sum_cons] at hs ⊢
      omega⟩
  | .inr c =>
    ⟨1 :: c.blocks, by simpa using fun i (hi : i ∈ c.blocks) => c.blocks_pos hi, by
      simp [Nat.add_comm]⟩

private theorem extend_bijective {n : ℕ} (hn : 1 ≤ n) : Function.Bijective (extend hn) := by
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  constructor
  · rintro ⟨_ | ⟨_ | _ | p, ps⟩, hp, hs⟩
    · simp at hs
    · simpa using hp List.mem_cons_self
    · refine ⟨.inr ⟨ps, fun hi => hp (List.mem_cons_of_mem _ hi), ?_⟩, rfl⟩
      simp only [List.sum_cons] at hs
      omega
    · refine ⟨.inl ⟨(p + 1) :: ps, ?_, ?_⟩, rfl⟩
      · simpa using fun i (hi : i ∈ ps) => hp (List.mem_cons_of_mem _ hi)
      · simp only [List.sum_cons] at hs ⊢
        omega
  · simp only [Fintype.card_sum, composition_card]
    rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ, Nat.mul_two]

/-- Sum a weight on lists of parts over all compositions of `n`. -/
private def total (f : List ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ c : Composition n, f c.blocks

private theorem total_succ (f : List ℕ → ℕ) {n : ℕ} (hn : 1 ≤ n) :
    total f (n + 1) = total (f ∘ bump) n + total (fun ps => f (1 :: ps)) n := by
  unfold total
  rw [← Equiv.sum_comp (Equiv.ofBijective (extend hn) (extend_bijective hn)),
    Fintype.sum_sum_type]
  congr 1
  apply Finset.sum_congr rfl
  rintro ⟨_ | ⟨p, ps⟩, _, hs⟩ _
  · simp at hs; omega
  · rfl

private theorem total_one (f : List ℕ → ℕ) : total f 1 = f [1] := by
  rw [total, Fintype.sum_eq_single (Composition.ones 1)]
  · rfl
  · intro c hc
    exact absurd (Composition.eq_ones_iff.2 fun i hi =>
      le_antisymm (c.blocks_le hi) (c.one_le_blocks hi)) hc

/-- Multiply alternate parts, starting at the first part if it is colored. -/
private def weight : Bool → List ℕ → ℕ
  | _, [] => 1
  | b, p :: ps => (if b then p else 1) * weight (!b) ps

/-- The odd colored weight with the first part's factor omitted, or zero for the empty list. -/
private def tailWeight : List ℕ → ℕ
  | [] => 0
  | _ :: ps => weight false ps

private theorem weight_eq_mapIdx (ps : List ℕ) (j : ℕ) :
    weight (decide (j % 2 = 0)) ps =
      (ps.mapIdx fun i p => if (i + j) % 2 = 0 then p else 1).prod := by
  induction ps generalizing j with
  | nil => simp [weight]
  | cons p ps ih =>
    have flip : (!decide (j % 2 = 0)) = decide ((j + 1) % 2 = 0) := by
      by_cases h : j % 2 = 0 <;> simp [h] <;> omega
    simp [weight, List.mapIdx_cons, flip, ih, Nat.add_left_comm, Nat.add_comm]

/-- Increasing an odd-colored part adds one copy of the weight of its tail. -/
private theorem composition_succ {n : ℕ} (hn : 1 ≤ n) :
    total (weight false) (n + 1) = total (weight false) n + total (weight true) n ∧
    total (weight true) (n + 1) =
      total (weight true) n + total tailWeight n + total (weight false) n ∧
    total tailWeight (n + 1) = total tailWeight n + total (weight false) n := by
  have he : weight false ∘ bump = weight false := by
    funext ps; cases ps <;> simp [weight, bump]
  have ho : weight true ∘ bump = fun ps => weight true ps + tailWeight ps := by
    funext ps; cases ps <;> simp [weight, bump, tailWeight, add_mul]
  have ht : tailWeight ∘ bump = tailWeight := by
    funext ps; cases ps <;> simp [tailWeight, bump]
  rw [total_succ (weight false) hn, total_succ (weight true) hn, total_succ tailWeight hn,
    he, ho, ht]
  simp [weight, tailWeight, total, Finset.sum_add_distrib]

/-- The suffix counts after letters `1`, `0`, and `2` satisfy the same recurrences as
the even weight, the odd weight, and the even weight plus the tail weight, respectively. -/
private theorem words_card_eq (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (Words n 1) = total (weight false) n ∧
    Nat.card (Words n 0) = total (weight true) n ∧
    Nat.card (Words n 2) = total (weight false) n + total tailWeight n := by
  induction n, hn using Nat.le_induction with
  | base =>
    simp [words_succ 0, Fin.sum_univ_three, step, words_zero, total_one, weight, tailWeight]
  | succ n hn ih =>
    obtain ⟨he, ho, ht⟩ := ih
    obtain ⟨re, ro, rt⟩ := composition_succ hn
    simp [words_succ n, Fin.sum_univ_three, step, he, ho, ht, re, ro, rt]
    omega

end even_eq_ternaryStrings_avoiding

open even_eq_ternaryStrings_avoiding in
/-- **Even colored compositions and ternary strings.** For every $k \ge 0$, the number
$e(k) = c_{2,0}(k)$ of even colored compositions of $k$, in which only the parts at even
positions are colored, equals the number of strings of length $k$ over the alphabet
$\{0, 1, 2\}$ that contain neither $01$ nor $12$ as two consecutive letters, do not begin with
$2$ and do not end with $0$.

At $k = 0$ both sides equal $1$, the empty string being counted.

Source: Andrew Li and Hua Wang, *Combinatorics of Positional Colored Compositions*, INTEGERS 26
(2026), Article A49, Theorem 3 (`integers-2026-A49-thm-3`). -/
public theorem even_eq_ternaryStrings_avoiding (k : ℕ) :
    positionalColoredCompositionCount 2 0 k =
      {w : List (Fin 3) | w.length = k ∧ ¬ [0, 1] <:+: w ∧ ¬ [1, 2] <:+: w ∧
        w.head? ≠ some 2 ∧ w.getLast? ≠ some 0}.ncard := by
  -- A preceding 1 rules out an initial 2 by the forbidden transition 12.
  have hWords : {w : List (Fin 3) | w.length = k ∧ ¬ [0, 1] <:+: w ∧
      ¬ [1, 2] <:+: w ∧ w.head? ≠ some 2 ∧ w.getLast? ≠ some 0}.ncard =
        Nat.card (Words k 1) := by
    rw [Set.ncard_ofPred]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro w
    cases w with
    | nil => simp [List.infix_cons_iff, List.cons_prefix_cons]
    | cons a w =>
      simp only [cons_valid, List.head?_cons, ne_eq, Option.some.injEq, step]
      simp
      tauto
  rw [hWords]
  cases k with
  | zero => simp [positionalColoredCompositionCount_zero, words_zero]
  | succ n =>
    rw [(words_card_eq (n + 1) (by omega)).1]
    apply Finset.sum_congr rfl
    intro c _
    simpa using (weight_eq_mapIdx c.blocks 1).symm

end MetaMathlibExt
