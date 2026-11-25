/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Words.RelativePositionBinaryWords

/-!
# Non-increasing relative positions in binary words

Every integer sequence that starts negative at index one and is non-increasing thereafter
is realized by the relative positions of a binary word starting with `b`.
-/

namespace MetaMathlibExt

namespace exists_word_relativePosition_eq_of_antitone

-- Positions occupied by the first n pairs, with occurrences numbered here from zero.
private def occupied (gap : ℕ → ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 =>
    let s := occupied gap n
    let b := Nat.find s.exists_notMem
    insert b (insert (b + gap n) s)

-- The least unused position becomes the next b, and its paired a lies gap n places later.
private theorem exists_complementary_positions (gap : ℕ → ℕ) (hpos : ∀ n, 0 < gap n) :
    ∃ b : ℕ → ℕ, StrictMono b ∧ b 0 = 0 ∧
      ∀ i, i ∈ Set.range b ↔ i ∉ Set.range (fun n => b n + gap n) := by
  let s := occupied gap
  let b (n : ℕ) := Nat.find (s n).exists_notMem
  let a (n : ℕ) := b n + gap n
  have step (n) : s (n + 1) = insert (b n) (insert (a n) (s n)) := rfl
  have fresh (n) : b n ∉ s n := Nat.find_spec (s n).exists_notMem
  have below {i n} (hi : i < b n) : i ∈ s n := by
    by_contra h
    exact hi.not_ge (Nat.find_min' (s n).exists_notMem h)
  have hb : StrictMono b := by
    apply strictMono_nat_of_lt_succ
    intro n
    have h := fresh (n + 1)
    rw [step] at h
    simp only [Finset.mem_insert, not_or] at h
    exact lt_of_le_of_ne (Nat.find_min' (s n).exists_notMem h.2.2) (Ne.symm h.1)
  have used (n i) : i ∈ s n ↔ ∃ k < n, i = b k ∨ i = a k := by
    induction n with
    | zero => simp [s, occupied]
    | succ n ih =>
      rw [step]
      simp only [Finset.mem_insert, ih]
      simp_rw [Nat.lt_succ_iff_lt_or_eq, or_and_right, exists_or]
      simp [or_assoc, or_comm]
  have hzero : b 0 = 0 :=
    Nat.le_zero.mp (Nat.find_min' (s 0).exists_notMem (by simp [s, occupied]))
  refine ⟨b, hb, hzero, fun i => ⟨?_, ?_⟩⟩
  · rintro ⟨n, rfl⟩ ⟨k, heq⟩
    change a k = b n at heq
    by_cases hk : k < n
    · exact fresh n ((used n _).2 ⟨k, hk, Or.inr heq.symm⟩)
    · have hle := hb.monotone (Nat.le_of_not_gt hk)
      have hlt : b k < a k := Nat.lt_add_of_pos_right (hpos k)
      omega
  · intro hi
    have hcovered := below (lt_of_lt_of_le i.lt_succ_self (hb.id_le (i + 1)))
    obtain ⟨k, _, h | h⟩ := (used _ _).1 hcovered
    · exact ⟨k, h.symm⟩
    · exact (hi ⟨k, h.symm⟩).elim

private theorem enumerate_positions {p : ℕ → Prop} {f : ℕ → ℕ}
    (hf : StrictMono f) (hr : Set.ofPred p = Set.range f) :
    (Set.ofPred p).Infinite ∧ Nat.nth p = f := by
  have hinf := hr ▸ Set.infinite_range_of_injective hf.injective
  exact ⟨hinf, ((Nat.nth_strictMono hinf).range_inj_of_wellFoundedLT hf).mp
    ((Nat.range_nth_of_infinite hinf).trans hr)⟩

end exists_word_relativePosition_eq_of_antitone

open exists_word_relativePosition_eq_of_antitone in
/-- **Non-increasing functions as relative position functions.** Let $r$ be a function from the
natural numbers to the integers with $r(1) < 0$ and $r(n+1) \le r(n)$ for every $n \ge 1$. Then
there is an infinite word $w$ over the letters $a$ and $b$ that starts with $b$, in which both
letters occur infinitely often, and whose relative position function satisfies $r_w(n) = r(n)$
for every $n \ge 1$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Corollary 9
(`jis-2025-25.1.5-cor-9`). -/
public theorem exists_word_relativePosition_eq_of_antitone (r : ℕ → ℤ) (h₁ : r 1 < 0)
    (hanti : ∀ n, 1 ≤ n → r (n + 1) ≤ r n) :
    ∃ w, BothLettersInfinite w ∧ w 0 = false ∧ ∀ n, 1 ≤ n → relativePosition w n = r n := by
  classical
  let gap (n : ℕ) := (-r (n + 1)).toNat
  have hr : Antitone (fun n => r (n + 1)) :=
    antitone_nat_of_succ_le fun n => hanti (n + 1) (by omega)
  have hneg (n : ℕ) : r (n + 1) < 0 := (hr (Nat.zero_le n)).trans_lt h₁
  have hpos (n) : 0 < gap n := by
    have := hneg n
    dsimp [gap]
    omega
  have hgap : Monotone gap := fun _ _ h => Int.toNat_le_toNat (Int.neg_le_neg (hr h))
  obtain ⟨b, hb, hzero, hcompl⟩ := exists_complementary_positions gap hpos
  let a (n : ℕ) := b n + gap n
  have ha : StrictMono a := fun _ _ h => Nat.add_lt_add_of_lt_of_le (hb h) (hgap h.le)
  let w (i : ℕ) := decide (i ∈ Set.range a)
  have hra : Set.ofPred (fun i => w i = true) = Set.range a := by ext i; simp [w]
  have hrb : Set.ofPred (fun i => w i = false) = Set.range b := by ext i; simp [w, hcompl, a]
  obtain ⟨hainf, hpa⟩ := enumerate_positions ha hra
  obtain ⟨hbinf, hpb⟩ := enumerate_positions hb hrb
  refine ⟨w, ⟨hainf, hbinf⟩, ?_, ?_⟩
  · change 0 ∈ Set.ofPred (fun i => w i = false)
    exact hrb.symm.subset ⟨0, hzero⟩
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp only [relativePosition, letterPosition, hpa, hpb, a]
    have := hneg k
    dsimp [gap]
    omega

end MetaMathlibExt
