/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import MathlibExt.NumberTheory.PierceExpansion

/-!
# Iterated remainder sets and the maximal Pierce length

For a natural number `n`, the iterated remainder sets `S_j(n)` start from
`S_0(n) = {1, …, ⌊n/2⌋}`, and `S_{j+1}(n)` collects the remainders `n mod k` of the nonzero
elements `k` of `S_j(n)`. The main result, `pierce_maxLength_eq_succ_iff`, shows that for `n ≥ 3`
the maximal Pierce length `P(n)` equals `t + 1` exactly when `S_t(n) = {0}`, and exactly when
`S_t(n)` has one element and all later sets are empty. This is Lemma 11 of Omkar Baraskar and
Ingrid Vukusic, *Bounds for sets of remainders*, arXiv:2508.20853v1 (2025), Section 5, with its
index corrected: the preprint prints it with `P(n) = t` and `S_{t+1}(n)`.

The proof identifies `S_j(n)` with the values at step `j` of the Pierce trajectories that start
in `{1, …, ⌊n/2⌋}` and do not reach `0` before step `j` (Lemma 10 of the preprint starts them in
`{⌊n/2⌋ + 1, …, n}` instead). For `n ≥ 3` it then shows that `P(n)` is one more than the largest
Pierce length of a starting value at most `⌊n/2⌋`: a starting value `a` with `⌊n/2⌋ < a < n`
first steps to `n - a ≤ ⌊n/2⌋`, every `b ≤ ⌊n/2⌋` with `2b < n` is reached in this way from
`n - b`, and for even `n` the value `b = n/2` has Pierce length `1`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Iterated remainder sets.** For a natural number $n$, the iterated remainder sets
$S_j(n)$, $j \ge 0$, are defined by $S_0(n) = \{1, \dots, \lfloor n/2 \rfloor\}$ and, for
$j \ge 0$, $S_{j+1}(n) = \{n \bmod k : k \in S_j(n),\ k \ne 0\}$.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Section 2 (definition of `S_j(n)`). -/
public def iteratedRemainderSet : ℕ → ℕ → Finset ℕ
  | 0, n => Finset.Icc 1 (n / 2)
  | j + 1, n => ((iteratedRemainderSet j n).erase 0).image (n % ·)

open PierceExpansion

/-- After `i` steps, a Pierce trajectory continues as the trajectory of its value at step `i`. -/
private theorem traj_add (n a i j : ℕ) : traj n a (i + j) = traj n (traj n a i) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← Nat.add_assoc]
    by_cases h : traj n a (i + j) = 0
    · have h' : traj n (traj n a i) j = 0 := by rwa [← ih]
      rw [traj_succ_of_eq_zero h, traj_succ_of_eq_zero h']
    · have h' : traj n (traj n a i) j ≠ 0 := by rwa [← ih]
      rw [traj_succ_of_ne_zero h, traj_succ_of_ne_zero h', ih]

/-- A trajectory from `a ≠ 0` avoids `0` before step `j` exactly when `j` is at most the Pierce
length of `a`. -/
private theorem forall_traj_ne_zero_iff {n a j : ℕ} (ha : a ≠ 0) :
    (∀ i < j, traj n a i ≠ 0) ↔ j ≤ length n a := by
  constructor
  · intro h
    by_contra hlt
    exact h _ (lt_of_not_ge hlt) (traj_length_eq_zero n a)
  · intro hj i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [traj_zero]
      exact ha
    · exact traj_ne_zero_of_lt_length hi0 (lt_of_lt_of_le hi hj)

/-- The elements of `S_j(n)` are the values at step `j` of the Pierce trajectories that start in
`{1, …, ⌊n/2⌋}` and have Pierce length at least `j`. -/
private theorem mem_iteratedRemainderSet_iff {n j r : ℕ} :
    r ∈ iteratedRemainderSet j n ↔
      ∃ a ∈ Finset.Icc 1 (n / 2), j ≤ length n a ∧ traj n a j = r := by
  suffices h : r ∈ iteratedRemainderSet j n ↔
      ∃ a ∈ Finset.Icc 1 (n / 2), (∀ i < j, traj n a i ≠ 0) ∧ traj n a j = r by
    rw [h]
    refine exists_congr fun a => and_congr_right fun ha => and_congr_left fun _ => ?_
    exact forall_traj_ne_zero_iff (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp ha).1)
  induction j generalizing r with
  | zero =>
    constructor
    · intro hr
      exact ⟨r, hr, fun i hi => absurd hi (Nat.not_lt_zero i), rfl⟩
    · rintro ⟨a, ha, -, rfl⟩
      exact ha
  | succ j ih =>
    simp only [iteratedRemainderSet, Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨k, ⟨hk0, hk⟩, rfl⟩
      obtain ⟨a, ha, hlt, rfl⟩ := ih.1 hk
      refine ⟨a, ha, fun i hi => ?_, traj_succ_of_ne_zero hk0⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact hlt i hi
      · exact hk0
    · rintro ⟨a, ha, hlt, rfl⟩
      have hj : traj n a j ≠ 0 := hlt j (Nat.lt_succ_self j)
      exact ⟨traj n a j, ⟨hj, ih.2 ⟨a, ha, fun i hi => hlt i (Nat.lt_succ_of_lt hi), rfl⟩⟩,
        (traj_succ_of_ne_zero hj).symm⟩

/-- For `n ≥ 2`, `S_t(n) = {0}` exactly when `t` is the largest Pierce length of a starting
value in `{1, …, ⌊n/2⌋}`. -/
private theorem iteratedRemainderSet_eq_singleton_zero_iff {n t : ℕ} (hn : 2 ≤ n) :
    iteratedRemainderSet t n = {0} ↔ (Finset.Icc 1 (n / 2)).sup (length n) = t := by
  constructor
  · intro h
    have h0 : (0 : ℕ) ∈ iteratedRemainderSet t n := by
      rw [h]
      exact Finset.mem_singleton_self 0
    obtain ⟨a, ha, hta, hat⟩ := mem_iteratedRemainderSet_iff.1 h0
    have ha0 : a ≠ 0 := Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp ha).1
    have ht : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · rw [traj_zero] at hat
        exact absurd hat ha0
      · exact ht
    have hlen : length n a = t := le_antisymm (length_le_of_traj_eq_zero ht hat) hta
    apply le_antisymm
    · apply Finset.sup_le
      intro b hb
      by_contra hlt
      have hlt' : t < length n b := lt_of_not_ge hlt
      have hmem : traj n b t ∈ iteratedRemainderSet t n :=
        mem_iteratedRemainderSet_iff.2 ⟨b, hb, hlt'.le, rfl⟩
      rw [h, Finset.mem_singleton] at hmem
      exact traj_ne_zero_of_lt_length ht hlt' hmem
    · rw [← hlen]
      exact Finset.le_sup ha
  · intro h
    ext r
    rw [Finset.mem_singleton, mem_iteratedRemainderSet_iff]
    constructor
    · rintro ⟨a, ha, hta, rfl⟩
      have hle : length n a ≤ t := h ▸ Finset.le_sup ha
      rw [← le_antisymm hle hta]
      exact traj_length_eq_zero n a
    · rintro rfl
      have hne : (Finset.Icc 1 (n / 2)).Nonempty := ⟨1, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩
      obtain ⟨a, ha, hsup⟩ := Finset.exists_mem_eq_sup _ hne (length n)
      rw [hsup] at h
      exact ⟨a, ha, h.ge, h ▸ traj_length_eq_zero n a⟩

/-- If `a ≠ 0` and `n mod a ≠ 0`, the Pierce length of `a` is one more than that of
`n mod a`. -/
private theorem length_eq_length_mod_add_one {n a : ℕ} (ha : a ≠ 0) (hr : n % a ≠ 0) :
    length n a = length n (n % a) + 1 := by
  have hshift : ∀ k, traj n a (k + 1) = traj n (n % a) k := by
    intro k
    rw [Nat.add_comm, traj_add, traj_one ha]
  apply le_antisymm
  · apply length_le_of_traj_eq_zero (Nat.le_add_left 1 _)
    rw [hshift]
    exact traj_length_eq_zero n (n % a)
  · have hm := length_pos n a
    have h0 := traj_length_eq_zero n a
    obtain ⟨k, hk⟩ : ∃ k, length n a = k + 1 := ⟨length n a - 1, by omega⟩
    rw [hk, hshift] at h0
    rw [hk]
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk1
      · rw [traj_zero] at h0
        exact absurd h0 hr
      · exact hk1
    exact Nat.succ_le_succ (length_le_of_traj_eq_zero hk1 h0)

/-- If `a ≠ 0` divides `n`, the Pierce length of `a` is `1`. -/
private theorem length_eq_one_of_mod_eq_zero {n a : ℕ} (ha : a ≠ 0) (hr : n % a = 0) :
    length n a = 1 :=
  le_antisymm (length_le_of_traj_eq_zero le_rfl (by rw [traj_one ha, hr])) (length_pos n a)

/-- For `n ≥ 3`, the maximal Pierce length of `n` is one more than the largest Pierce length of a
starting value in `{1, …, ⌊n/2⌋}`. -/
private theorem maxLength_eq_sup_add_one {n : ℕ} (hn : 3 ≤ n) :
    maxLength n = (Finset.Icc 1 (n / 2)).sup (length n) + 1 := by
  apply le_antisymm
  · apply maxLength_le_of_forall
    intro a ha
    rw [Finset.mem_Icc] at ha
    by_cases hah : a ≤ n / 2
    · exact (Finset.le_sup (f := length n) (Finset.mem_Icc.2 ⟨ha.1, hah⟩)).trans
        (Nat.le_succ _)
    · have ha0 : a ≠ 0 := by omega
      have hmod : n % a = n - a := by
        rw [Nat.mod_eq_sub_mod ha.2, Nat.mod_eq_of_lt (by omega)]
      by_cases hr : n % a = 0
      · rw [length_eq_one_of_mod_eq_zero ha0 hr]
        omega
      · rw [length_eq_length_mod_add_one ha0 hr]
        have hmem : n % a ∈ Finset.Icc 1 (n / 2) := by
          rw [Finset.mem_Icc, hmod]
          omega
        exact Nat.succ_le_succ (Finset.le_sup hmem)
  · have key : ∀ b ∈ Finset.Icc 1 (n / 2), length n b < maxLength n := by
      intro b hb
      rw [Finset.mem_Icc] at hb
      by_cases h2b : 2 * b < n
      · have hab : n % (n - b) = b := by
          rw [Nat.mod_eq_sub_mod (Nat.sub_le n b), Nat.sub_sub_self (by omega),
            Nat.mod_eq_of_lt (by omega)]
        have hlen := length_eq_length_mod_add_one (n := n) (a := n - b) (by omega)
          (by rw [hab]; omega)
        rw [hab] at hlen
        have hle := length_le_maxLength (n := n) (a := n - b)
          (Finset.mem_Icc.2 ⟨by omega, Nat.sub_le n b⟩)
        omega
      · have hb1 : length n b = 1 := length_eq_one_of_mod_eq_zero (by omega)
          (by rw [show n = b * 2 by omega, Nat.mul_mod_right])
        have hn1 : n % (n - 1) = 1 := by
          rw [Nat.mod_eq_sub_mod (Nat.sub_le n 1), Nat.sub_sub_self (by omega),
            Nat.mod_eq_of_lt (by omega)]
        have hlen := length_eq_length_mod_add_one (n := n) (a := n - 1) (by omega)
          (by rw [hn1]; omega)
        have hle := length_le_maxLength (n := n) (a := n - 1)
          (Finset.mem_Icc.2 ⟨by omega, Nat.sub_le n 1⟩)
        have hpos := length_pos n (n % (n - 1))
        omega
    have hbot : (⊥ : ℕ) < maxLength n :=
      bot_le.trans_lt (key 1 (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩))
    have hlt := (Finset.sup_lt_iff hbot).2 key
    omega

/-- **Maximal Pierce length via iterated remainder sets.** Let $n \ge 3$ and $t$ be natural
numbers, let $P(n)$ be the maximal Pierce length of $n$ and let $S_j(n)$ be the iterated
remainder sets of $n$. Then the following are equivalent: $P(n) = t + 1$; $S_t(n) = \{0\}$;
$S_t(n)$ has exactly one element and $S_{t+j}(n) = \emptyset$ for every $j \ge 1$.

This corrects the index of the printed lemma, $P(n) = t \iff S_{t+1}(n) = \{0\}$, which fails
for every $n \ge 3$: for example $P(5) = 3$, $S_2(5) = \{0\}$ and $S_4(5) = \emptyset$. The
paper derives the lemma from its Lemma 18 ($r \in S_j(n)$ if and only if $a_{j+1} = r$ for some
$\lfloor n/2 \rfloor + 1 \le a \le n$, where $a_0 = a$ and $a_{i+1} = n \bmod a_i$), which
gives the index $P(n) - 1$. Lemma 18, and hence this lemma, needs $n \ge 3$: $P(2) = 1$ but
$S_0(2) = \{1\}$.

Source: the forward direction of the first equivalence (for `t ≥ 1`) is proved as
`S_eq_singleton_zero_of_maxLength_eq` in
`FormalizedPapers/NumberTheory/BaraskarGokhaleJainKiezun2026`.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Lemma 19. -/
public theorem pierce_maxLength_eq_succ_iff (n t : ℕ) (hn : 3 ≤ n) :
    (PierceExpansion.maxLength n = t + 1 ↔ iteratedRemainderSet t n = {0}) ∧
      (PierceExpansion.maxLength n = t + 1 ↔ (iteratedRemainderSet t n).card = 1 ∧
        ∀ j, 1 ≤ j → iteratedRemainderSet (t + j) n = ∅) := by
  have hsing := iteratedRemainderSet_eq_singleton_zero_iff (t := t) (by omega : 2 ≤ n)
  have hP : maxLength n = t + 1 ↔ (Finset.Icc 1 (n / 2)).sup (length n) = t := by
    rw [maxLength_eq_sup_add_one hn, add_left_inj]
  refine ⟨hP.trans hsing.symm, hP.trans ?_⟩
  constructor
  · intro h
    refine ⟨by rw [hsing.2 h, Finset.card_singleton], fun j hj => ?_⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro r hr
    obtain ⟨a, ha, hle, -⟩ := mem_iteratedRemainderSet_iff.1 hr
    have hsup := Finset.le_sup (f := length n) ha
    omega
  · rintro ⟨hcard, hempty⟩
    obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hcard
    have hxmem : x ∈ iteratedRemainderSet t n := by
      rw [hx]
      exact Finset.mem_singleton_self x
    obtain ⟨a, ha, hta, -⟩ := mem_iteratedRemainderSet_iff.1 hxmem
    apply le_antisymm
    · apply Finset.sup_le
      intro b hb
      by_contra hlt
      have hmem : traj n b (t + 1) ∈ iteratedRemainderSet (t + 1) n :=
        mem_iteratedRemainderSet_iff.2 ⟨b, hb, lt_of_not_ge hlt, rfl⟩
      rw [hempty 1 le_rfl] at hmem
      exact Finset.notMem_empty _ hmem
    · exact hta.trans (Finset.le_sup ha)

end

end MetaMathlibExt
