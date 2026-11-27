/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.Combinatorics.Enumerative.RascalWords
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Digits.Lemmas

/-! # Binomial sum for generalized Rascal numbers

We count the words with exactly `i` ascents by splitting on their first bit and using
Pascal's identity. An extra bit to the left records whether prepending a `1` creates
an ascent; taking that extra bit to be `1` leaves the ascent count unchanged.
-/

namespace MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted

open List

private abbrev Binary (w : List ℕ) : Prop := ∀ x ∈ w, x = 0 ∨ x = 1

-- Here `z` and `k` count only the zeros and ones of `w`, not the extra bit `b`.
private noncomputable def exactWords (b z k i : ℕ) : Finset (List ℕ) :=
  (fixedLengthDigits (b := 2) (by decide) (z + k)).filter
    (fun w => w.count 1 = k ∧ wordAscents (b :: w) = i)

private theorem mem_exactWords {b z k i : ℕ} {w : List ℕ} :
    w ∈ exactWords b z k i ↔
      w.length = z + k ∧ Binary w ∧ w.count 1 = k ∧ wordAscents (b :: w) = i := by
  have bit (x : ℕ) : x < 2 ↔ x = 0 ∨ x = 1 := by omega
  simp [exactWords, mem_fixedLengthDigits_iff, Binary, bit, and_assoc]

private theorem ascents_replicate (a n : ℕ) : wordAscents (replicate n a) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      change (if a < a then 1 else 0) + wordAscents (replicate (n + 1) a) = 0
      rwa [ite_eq_right (lt_irrefl a), Nat.zero_add]

private theorem ascents_cons_replicate (b a n : ℕ) :
    wordAscents (b :: replicate (n + 1) a) = if b < a then 1 else 0 := by
  change (if b < a then 1 else 0) + wordAscents (replicate (n + 1) a) = _
  rw [ascents_replicate, Nat.add_zero]

private theorem card_exactWords_zero_ones (b z i : ℕ) :
    (exactWords b z 0 i).card = if i = 0 then 1 else 0 := by
  have ascent : wordAscents (b :: replicate z 0) = 0 := by
    cases z <;> simp [ascents_cons_replicate, wordAscents]
  have mem (w : List ℕ) : w ∈ exactWords b z 0 i ↔ w = replicate z 0 ∧ i = 0 := by
    rw [mem_exactWords]
    constructor
    · rintro ⟨hlen, hw, hk, hi⟩
      have he : w = replicate z 0 := by
        rw [← show w.length = z by simpa using hlen]
        exact eq_replicate_of_mem fun x hx => (hw x hx).resolve_right fun h =>
          not_mem_of_count_eq_zero hk (h ▸ hx)
      exact ⟨he, hi.symm.trans (he ▸ ascent)⟩
    · rintro ⟨rfl, rfl⟩
      simp [Binary, ascent, count_replicate]
  have he : exactWords b z 0 i = if i = 0 then {replicate z 0} else ∅ := by
    ext w
    rw [mem]
    split <;> simp_all
  rw [he]
  split <;> simp

private theorem card_exactWords_zero_zeros (b k i : ℕ) :
    (exactWords b 0 k i).card = if i = (if k = 0 then 0 else if b < 1 then 1 else 0)
      then 1 else 0 := by
  let r := if k = 0 then 0 else if b < 1 then 1 else 0
  change (exactWords b 0 k i).card = if i = r then 1 else 0
  have ascent : wordAscents (b :: replicate k 1) = r := by
    cases k <;> simp [r, ascents_cons_replicate, wordAscents]
  have mem (w : List ℕ) : w ∈ exactWords b 0 k i ↔ w = replicate k 1 ∧ i = r := by
    rw [mem_exactWords]
    constructor
    · rintro ⟨hlen, _, hk, hi⟩
      have he : w = replicate k 1 := by
        rw [← hk]
        exact (replicate_count_eq_of_count_eq_length (hk.trans (by simpa using hlen.symm))).symm
      exact ⟨he, hi.symm.trans (he ▸ ascent)⟩
    · rintro ⟨rfl, rfl⟩
      simp [Binary, ascent]
  have he : exactWords b 0 k i = if i = r then {replicate k 1} else ∅ := by
    ext w
    rw [mem]
    split <;> simp_all
  rw [he]
  split <;> simp

private def consBit (b : ℕ) : List ℕ ↪ List ℕ :=
  ⟨(b :: ·), fun _ _ h => (List.cons.inj h).2⟩

private theorem mem_map_consBit {b : ℕ} {s : Finset (List ℕ)} {w : List ℕ} :
    w ∈ s.map (consBit b) ↔ ∃ v ∈ s, b :: v = w := by
  rw [Finset.mem_map]
  rfl

-- The zero prefix costs no ascent. The one prefix costs one exactly when `b = 0`.
private theorem card_exactWords_succ_succ (b z k i : ℕ) :
    let d : ℕ := if b < 1 then 1 else 0
    (exactWords b (z + 1) (k + 1) i).card = (exactWords 0 z (k + 1) i).card +
      (if d ≤ i then (exactWords 1 (z + 1) k (i - d)).card else 0) := by
  intro d
  let zeros := (exactWords 0 z (k + 1) i).map (consBit 0)
  let ones := if d ≤ i then (exactWords 1 (z + 1) k (i - d)).map (consBit 1) else ∅
  have disj : Disjoint zeros ones := by
    by_cases h : d ≤ i
    · simp only [zeros, ones, ite_eq_left h, Finset.disjoint_left, mem_map_consBit]
      rintro _ ⟨w, _, rfl⟩ ⟨v, _, e⟩
      simp at e
    · simp [ones, h]
  have he : exactWords b (z + 1) (k + 1) i = zeros.disjUnion ones disj := by
    ext w
    simp only [mem_exactWords, Finset.mem_disjUnion, zeros, ones,
      apply_ite (fun s : Finset (List ℕ) => w ∈ s), Finset.notMem_empty, mem_map_consBit]
    cases w with
    | nil => simp
    | cons x w =>
      by_cases hx : x = 0 ∨ x = 1
      · rcases hx with rfl | rfl
        · have hl : w.length + 1 = z + 1 + (k + 1) ↔ w.length = z + (k + 1) := by omega
          simp [wordAscents, Binary, hl]
        · have hl : w.length + 1 = z + 1 + (k + 1) ↔ w.length = z + 1 + k := by omega
          have ha : wordAscents (b :: 1 :: w) = d + wordAscents (1 :: w) := rfl
          by_cases h : d ≤ i
          · have hr : d + wordAscents (1 :: w) = i ↔ wordAscents (1 :: w) = i - d := by
              omega
            simp [Binary, hl, ha, hr, h]
          · have hr : d + wordAscents (1 :: w) ≠ i := by omega
            simp [ha, hr, h]
      · have h0 : 0 ≠ x := fun h => hx (Or.inl h.symm)
        have h1 : 1 ≠ x := fun h => hx (Or.inr h.symm)
        simp [Binary, hx, h0, h1]
  rw [he, Finset.card_disjUnion]
  by_cases h : d ≤ i <;> simp [zeros, ones, h]

-- The two prefix states satisfy Pascal's identity in different variables.
private theorem card_exactWords (z k i : ℕ) :
    (exactWords 1 z k i).card = z.choose i * k.choose i ∧
    (exactWords 0 z k 0).card = (if k = 0 then 1 else 0) ∧
    (exactWords 0 z k (i + 1)).card =
      (if k = 0 then 0 else (z + 1).choose (i + 1) * (k - 1).choose i) := by
  induction z generalizing k i with
  | zero => cases k <;> cases i <;> simp [card_exactWords_zero_zeros, Nat.choose_eq_zero_of_lt]
  | succ z ihz =>
    induction k generalizing i with
    | zero => cases i <;> simp [card_exactWords_zero_ones]
    | succ k ihk =>
      refine ⟨?_, ?_, ?_⟩
      · cases i with
        | zero => simp [card_exactWords_succ_succ, (ihz (k + 1) 0).2.1, (ihk 0).1]
        | succ i =>
          simp [card_exactWords_succ_succ, (ihz (k + 1) i).2.2, (ihk (i + 1)).1,
            Nat.choose_succ_succ k i, Nat.mul_add]
      · simp [card_exactWords_succ_succ, (ihz (k + 1) 0).2.1]
      · have pascal : (1 + (z + 1)).choose (i + 1) =
            (z + 1).choose i + (z + 1).choose (i + 1) := by
          rw [Nat.add_comm 1 (z + 1), Nat.choose_succ_succ]
        simp [card_exactWords_succ_succ, (ihz (k + 1) i).2.2, (ihk i).1,
          pascal, Nat.add_mul, Nat.add_comm]

private theorem ascents_cons_one {w : List ℕ} (hw : Binary w) :
    wordAscents (1 :: w) = wordAscents w := by
  cases w with
  | nil => rfl
  | cons x w =>
    obtain rfl | rfl := hw x (by simp)
    all_goals simp [wordAscents]

/-- **Generalized Rascal numbers as sums of products of binomial coefficients.** For all natural
numbers $j$, $n$ and $k$ with $k \le n$, the generalized Rascal number $R^{(j)}_{n,k}$, the
number of binary words of length $n$ with exactly $k$ ones and at most $j$ ascents (positions
where a $0$ is immediately followed by a $1$), equals
$\sum_{i=0}^{j} \binom{k}{i} \binom{n-k}{i}$.

The hypothesis $k \le n$ is needed: for $k > n$ the left side is $0$, while the right side,
with $n - k$ read as $0$, is $1$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 19. -/
public theorem rascalGen_eq_sum (j n k : ℕ) (hkn : k ≤ n) :
    (rascalGen j k n : ℤ) =
      ∑ i ∈ Finset.range (j + 1),
        (Nat.choose k i : ℤ) * (Nat.choose (n - k) i : ℤ) := by
  let words := (fixedLengthDigits (b := 2) (by decide) n).filter (fun w => w.count 1 = k)
  have mem (w : List ℕ) : w ∈ words ↔ w.length = n ∧ Binary w ∧ w.count 1 = k := by
    have bit (x : ℕ) : x < 2 ↔ x = 0 ∨ x = 1 := by omega
    simp [words, mem_fixedLengthDigits_iff, Binary, bit, and_assoc]
  have hcard : rascalGen j k n = (words.filter fun w =>
      wordAscents (1 :: w) ∈ Finset.range (j + 1)).card := by
    apply Nat.subtype_card
    intro w
    rw [Finset.mem_filter, mem, Finset.mem_range, Nat.lt_succ_iff]
    by_cases hw : Binary w
    · simp [ascents_cons_one hw, and_assoc]
    · simp [hw]
  have hfiber (i : ℕ) : words.filter (fun w => wordAscents (1 :: w) = i) =
      exactWords 1 (n - k) k i := by
    ext w
    simp [mem_exactWords, mem, Nat.sub_add_cancel hkn, and_assoc]
  rw [hcard, ← Finset.sum_card_fiberwise_eq_card_filter]
  simp_rw [hfiber, (card_exactWords (n - k) k _).1, mul_comm (Nat.choose (n - k) _),
    Nat.cast_sum, Nat.cast_mul]

end MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted
