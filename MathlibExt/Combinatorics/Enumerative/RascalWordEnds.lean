/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.RascalNumbers
public import MathlibExt.Combinatorics.Enumerative.RascalWords
import Mathlib.Data.Fintype.Option

/-!
# Rascal words with prescribed ends

`card_prefixOnes_suffixZeros` counts the words with at most one ascent after fixing
an initial block of ones and a terminal block of zeros.
-/

namespace MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted

open List

private abbrev Binary (w : List ℕ) : Prop := ∀ x ∈ w, x = 0 ∨ x = 1

private theorem ascents_cons_one {w : List ℕ} (hw : Binary w) :
    wordAscents (1 :: w) = wordAscents w := by
  cases w with
  | nil => rfl
  | cons x xs =>
    obtain rfl | rfl := hw x (by simp)
    all_goals simp [wordAscents]

private theorem ascents_ones_append (a : ℕ) {w : List ℕ} (hw : Binary w) :
    wordAscents (replicate a 1 ++ w) = wordAscents w := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [replicate_succ, cons_append, ascents_cons_one, ih]
    intro x hx
    rcases mem_append.mp hx with hx | hx
    · exact Or.inr (eq_of_mem_replicate hx)
    · exact hw x hx

private theorem ascents_replicate (n x : ℕ) : wordAscents (replicate n x) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => cases n <;> simp_all [replicate_succ, wordAscents]

private theorem ascents_append_zeros (w : List ℕ) (d : ℕ) :
    wordAscents (w ++ replicate d 0) = wordAscents w := by
  induction w using wordAscents.induct with
  | case1 => simpa [wordAscents] using ascents_replicate d 0
  | case2 a =>
    cases d with
    | zero => rfl
    | succ d =>
      simpa [replicate_succ, wordAscents] using ascents_replicate (d + 1) 0
  | case3 a b t ih => simpa [wordAscents] using ih

private def descending (a d : ℕ) : List ℕ := replicate a 1 ++ replicate d 0

-- The two inner runs are nonempty, so their boundary is the unique ascent.
private def oneAscent (a b c d : ℕ) : List ℕ :=
  replicate a 1 ++ (replicate (b + 1) 0 ++ (replicate (c + 1) 1 ++ replicate d 0))

private theorem ascents_descending (a d : ℕ) : wordAscents (descending a d) = 0 := by
  rw [descending, ascents_append_zeros]
  exact ascents_replicate a 1

private theorem ascents_oneAscent (a b c d : ℕ) : wordAscents (oneAscent a b c d) = 1 := by
  rw [oneAscent, ascents_ones_append, ← append_assoc, ascents_append_zeros]
  · induction b with
    | zero =>
      change 1 + wordAscents (replicate (c + 1) 1) = 1
      rw [ascents_replicate, Nat.add_zero]
    | succ b ih =>
      simpa [replicate_succ, wordAscents] using ih
  · simp [Binary]

private theorem word_forms {w : List ℕ} (hw : Binary w) (h : wordAscents w ≤ 1) :
    (∃ a d, w = descending a d) ∨ (∃ a b c d, w = oneAscent a b c d) := by
  induction w with
  | nil => exact Or.inl ⟨0, 0, rfl⟩
  | cons x w ih =>
    have htail : wordAscents w ≤ wordAscents (x :: w) := by
      cases w <;> simp [wordAscents]
    specialize ih (fun y hy => hw y (mem_cons_of_mem _ hy)) (htail.trans h)
    obtain rfl | rfl := hw x (by simp)
    all_goals obtain ⟨a, d, rfl⟩ | ⟨a, b, c, d, rfl⟩ := ih
    · cases a with
      | zero => exact Or.inl ⟨0, d + 1, by simp [descending, replicate_succ]⟩
      | succ a => exact Or.inr ⟨0, 0, a, d, by simp [descending, oneAscent]⟩
    · cases a with
      | zero => exact Or.inr ⟨0, b + 1, c, d, by simp [oneAscent, replicate_succ]⟩
      | succ a =>
        have ha := ascents_oneAscent (a + 1) b c d
        have he : wordAscents (0 :: oneAscent (a + 1) b c d) =
            1 + wordAscents (oneAscent (a + 1) b c d) := by
          simp [oneAscent, replicate_succ, wordAscents]
        omega
    · exact Or.inl ⟨a + 1, d, by simp [descending, replicate_succ]⟩
    · exact Or.inr ⟨a + 1, b, c, d, by simp [oneAscent, replicate_succ]⟩

-- The length of the initial run is the index of the first opposite bit.
private theorem take_run {w : List ℕ} {i x y : ℕ} (hxy : x ≠ y)
    (hw : ∀ z ∈ w, z = x ∨ z = y) (hi : i ≤ w.length) :
    (∀ z ∈ w.take i, z = x) ↔ i ≤ w.idxOf y := by
  by_cases hy : y ∈ w
  · rw [← not_lt, ← mem_take_iff_idxOf_lt hy]
    constructor
    · exact fun h hm => hxy (h _ hm).symm
    · intro h z hz
      exact (hw z (mem_of_mem_take hz)).resolve_right (fun e => h (e ▸ hz))
  · rw [idxOf_eq_length_iff.mpr hy]
    exact iff_of_true (fun z hz => (hw z (mem_of_mem_take hz)).resolve_right
      (fun e => hy (e ▸ mem_of_mem_take hz))) hi

private abbrev Valid (n k ℓ u : ℕ) (w : List ℕ) : Prop :=
  (w.length = n ∧ Binary w ∧ w.count 1 = k ∧ wordAscents w ≤ 1) ∧
    (∀ x ∈ w.take ℓ, x = 1) ∧ (∀ x ∈ w.drop (n - u), x = 0)

private theorem valid_iff {n k ℓ u : ℕ} {w : List ℕ} (hℓ : ℓ ≤ n) (hu : u ≤ n)
    (hb : Binary w) (ha : wordAscents w ≤ 1) :
    Valid n k ℓ u w ↔
      w.length = n ∧ w.count 1 = k ∧ ℓ ≤ w.idxOf 0 ∧ u ≤ w.reverse.idxOf 1 := by
  unfold Valid
  by_cases hn : w.length = n
  · have hp := take_run (x := 1) (y := 0) (by decide) (fun x hx => (hb x hx).symm)
      (hn ▸ hℓ : ℓ ≤ w.length)
    have hs := take_run (x := 0) (y := 1) (by decide)
      (fun x (hx : x ∈ w.reverse) => hb x (mem_reverse.mp hx))
      (by simpa [hn] using hu : u ≤ w.reverse.length)
    rw [take_reverse, hn] at hs
    simp only [mem_reverse] at hs
    exact ⟨fun ⟨⟨_, _, hc, _⟩, h₁, h₀⟩ => ⟨hn, hc, hp.mp h₁, hs.mp h₀⟩,
      fun ⟨_, hc, h₁, h₀⟩ => ⟨⟨hn, hb, hc, ha⟩, hp.mpr h₁, hs.mpr h₀⟩⟩
  · simp [hn]

private theorem descending_indices (a d : ℕ) :
    (descending a d).idxOf 0 = a ∧ (descending a d).reverse.idxOf 1 = d := by
  have run (n x : ℕ) : (replicate n x).idxOf x = 0 := by
    cases n <;> simp [replicate_succ]
  simp [descending, idxOf_append_of_notMem, run]

private theorem oneAscent_indices (a b c d : ℕ) :
    (oneAscent a b c d).idxOf 0 = a ∧ (oneAscent a b c d).reverse.idxOf 1 = d := by
  simp [oneAscent, append_assoc, idxOf_append_of_notMem, replicate_succ (n := b),
    replicate_succ (n := c), reverse_cons, ← replicate_succ']

private theorem valid_descending {n k ℓ u a d : ℕ} (hℓ : ℓ ≤ n) (hu : u ≤ n) :
    Valid n k ℓ u (descending a d) ↔ a + d = n ∧ a = k ∧ ℓ ≤ a ∧ u ≤ d := by
  rw [valid_iff hℓ hu (by simp [Binary, descending]; grind) (by simp [ascents_descending]),
    (descending_indices a d).1, (descending_indices a d).2]
  simp [descending, count_replicate]

private theorem valid_oneAscent {n k ℓ u a b c d : ℕ} (hℓ : ℓ ≤ n) (hu : u ≤ n) :
    Valid n k ℓ u (oneAscent a b c d) ↔
      a + (b + 1 + (c + 1 + d)) = n ∧ a + (c + 1) = k ∧ ℓ ≤ a ∧ u ≤ d := by
  rw [valid_iff hℓ hu (by simp [Binary, oneAscent]; grind) (by simp [ascents_oneAscent]),
    (oneAscent_indices a b c d).1, (oneAscent_indices a b c d).2]
  simp [oneAscent, count_replicate]

-- For a word with one ascent, the coordinates count the extra initial ones and final zeros.
private def encode (n k ℓ u : ℕ) : Option (Fin (k - ℓ) × Fin (n - k - u)) → List ℕ
  | none => descending k (n - k)
  | some (i, j) =>
    oneAscent (ℓ + i) (n - k - (u + j + 1)) (k - (ℓ + i + 1)) (u + j)

private theorem encode_valid {n k ℓ u : ℕ} (hℓ : ℓ ≤ k) (hu : k + u ≤ n)
    (s : Option (Fin (k - ℓ) × Fin (n - k - u))) : Valid n k ℓ u (encode n k ℓ u s) := by
  rcases s with _ | ⟨i, j⟩
  · apply (valid_descending (by omega) (by omega)).mpr
    omega
  · apply (valid_oneAscent (by omega) (by omega)).mpr
    have := i.isLt
    have := j.isLt
    omega

private theorem encode_injective (n k ℓ u : ℕ) : Function.Injective (encode n k ℓ u) := by
  rintro (_ | ⟨i, j⟩) (_ | ⟨i', j'⟩) h
  · rfl
  · simpa [encode, ascents_descending, ascents_oneAscent] using congrArg wordAscents h
  · simpa [encode, ascents_descending, ascents_oneAscent] using congrArg wordAscents h
  · have h₁ := congrArg (idxOf 0) h
    have h₀ := congrArg (fun w => w.reverse.idxOf 1) h
    simp only [encode, (oneAscent_indices ..).1, (oneAscent_indices ..).2,
      Nat.add_left_cancel_iff] at h₁ h₀
    rw [Fin.ext h₁, Fin.ext h₀]

private theorem exists_encode {n k ℓ u : ℕ} (hℓ : ℓ ≤ k) (hu : k + u ≤ n)
    {w : List ℕ} (hw : Valid n k ℓ u w) : ∃ s, encode n k ℓ u s = w := by
  obtain ⟨a, d, rfl⟩ | ⟨a, b, c, d, rfl⟩ := word_forms hw.1.2.1 hw.1.2.2.2
  · obtain ⟨hlen, rfl, _, _⟩ := (valid_descending (by omega) (by omega)).mp hw
    exact ⟨none, by simp [encode, ← hlen]⟩
  · obtain ⟨hlen, hc, ha, hd⟩ := (valid_oneAscent (by omega) (by omega)).mp hw
    refine ⟨some (⟨a - ℓ, by omega⟩, ⟨d - u, by omega⟩), ?_⟩
    simp only [encode]
    congr 1 <;> omega

/-- **Binary words with a prefix of ones and a suffix of zeros.** Let $n, k, \ell, u$ be natural
numbers with $\ell \le k$ and $k + u \le n$, and let $B_k(n)$ be the set of binary words $w$ of
length $n$ with exactly $k$ ones and at most one ascent (a position $i$ with $w_i < w_{i+1}$).
The number of words in $B_k(n)$ whose first $\ell$ letters are all $1$ and whose last $u$
letters are all $0$ equals the Rascal number $R_{n-u-\ell, k-\ell}$, where
$R_{a,b} = b(a-b) + 1$ for $0 \le b \le a$.

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Lemma 3. -/
public theorem card_prefixOnes_suffixZeros (n k ℓ u : ℕ)
    (hℓ : ℓ ≤ k) (hu : k + u ≤ n) :
    (Nat.card { w : RascalWord 1 k n //
        (∀ x ∈ w.1.take ℓ, x = 1) ∧
          (∀ x ∈ w.1.drop (n - u), x = 0) } : ℤ) =
      rascalZ (n - u - ℓ : ℕ) (k - ℓ : ℕ) := by
  let word (s : Option (Fin (k - ℓ) × Fin (n - k - u))) :
      { w : RascalWord 1 k n // (∀ x ∈ w.1.take ℓ, x = 1) ∧
        (∀ x ∈ w.1.drop (n - u), x = 0) } :=
    ⟨⟨encode n k ℓ u s, (encode_valid hℓ hu s).1⟩, (encode_valid hℓ hu s).2⟩
  have hbij : Function.Bijective word := by
    constructor
    · intro s t h
      exact encode_injective n k ℓ u (congrArg (fun w => w.1.1) h)
    · intro w
      obtain ⟨s, hs⟩ := exists_encode hℓ hu ⟨w.1.2, w.2⟩
      exact ⟨s, Subtype.ext (Subtype.ext hs)⟩
  rw [← Nat.card_eq_of_bijective word hbij, Nat.card_eq_fintype_card]
  have hkn : k - ℓ ≤ n - u - ℓ := by omega
  rw [show n - k - u = (n - u - ℓ) - (k - ℓ) by omega]
  simp [rascalZ, hkn, Int.ofNat_sub hkn]

/-- **Rascal numbers count binary words with at most one ascent.** For all integers $n$ and $k$,
$R_{n,k} = b_k(n)$, where $R_{n,k}$ is the Rascal number and $b_k(n)$ is the number of binary
words of length $n$ with exactly $k$ ones and at most one ascent (taken to be $0$ unless
$0 \le k \le n$).

Source: Amelia Gibbs and Brian K. Miceli, "Two Combinatorial
Interpretations of Rascal Numbers", Theorem 1. -/
public theorem rascalZ_eq_rascalGenZ_one (n k : ℤ) :
    rascalZ n k = rascalGenZ 1 n k := by
  by_cases h : 0 ≤ k ∧ k ≤ n
  · have hEnds (w : RascalWord 1 k.toNat n.toNat) :
        (∀ x ∈ w.1.take 0, x = 1) ∧ (∀ x ∈ w.1.drop n.toNat, x = 0) := by
      simp [← w.2.1]
    have hcount := card_prefixOnes_suffixZeros n.toNat k.toNat 0 0 (Nat.zero_le _)
      (by simpa using Int.toNat_le_toNat h.2)
    simp only [Nat.sub_zero, Nat.card_congr (Equiv.subtypeUnivEquiv hEnds),
      Int.toNat_of_nonneg h.1, Int.toNat_of_nonneg (h.1.trans h.2)] at hcount
    simpa only [rascalGenZ, ite_eq_left h, rascalGen] using hcount.symm
  · simp [rascalZ, rascalGenZ, h]

end MathlibExt.Combinatorics.Enumerative.RascalNumbersWanted
