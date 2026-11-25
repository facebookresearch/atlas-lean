/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.ManyThreeTermProgressionsErdosProblem179
import MathlibExt.Combinatorics.DensityHalesJewett
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa

/-!
# Four-term progressions forced by many three-term progressions

The threshold for forcing a four-term progression from three-term progressions is subquadratic.

When a set has quadratically many three-term progressions, the graph joining their endpoints
has positive edge density. Counting common neighbors gives a large subset with a small
difference set. Repeated intersections with translates put a binary cube inside this subset.
Plünnecke–Ruzsa controls the number of translates of the corresponding four-letter cube
that meet the subset, and density Hales–Jewett gives a four-term progression in one of them.

Source: T. F. Bloom, Erdős Problems, Problem #179, https://www.erdosproblems.com/179 (status
PROVED). UnsolvedMath record UM-30006752 (`EP-179`), dataset ulamai/UnsolvedMath v1.8.0.

Sets are finite subsets of `ℕ` (the count is translation invariant). A `k`-term progression is a
pair `(a, d)` with `d ≥ 1` and `a + i d ∈ A` for `i < k`; for `k ≥ 2` such `a, d` are at most `max
A` and `(a, d) ↦ (a, a + d)` is injective, so the count is at most `N²`, `F_k(N, ℓ)` is the infimum
of a nonempty set, and `F₃(N, ℓ) ≥ 1` (sets of powers of `2` have no `3`-term progression). The
open-ended "find good upper bounds" is not formalized.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ManyThreeTermProgressionsErdosProblem179Wanted

open Finset
open scoped Pointwise

-- Count differences with multiplicity. Summing over any set of differences costs at
-- most the total number of ordered pairs.
private def reps (S : Finset ℤ) (d : ℤ) : Finset (ℤ × ℤ) :=
  (S ×ˢ S).filter fun p => p.1 - p.2 = d

private lemma sum_reps_le (S D : Finset ℤ) : ∑ d ∈ D, (reps S d).card ≤ S.card ^ 2 := by
  simpa [reps, sum_card_fiberwise_eq_card_filter, sq] using
    (card_filter_le (S ×ˢ S) (fun p => p.1 - p.2 ∈ D))

private lemma popular_bound {S D : Finset ℤ} {n k : ℕ}
    (h : ∀ d ∈ D, n ≤ k * (reps S d).card) : D.card * n ≤ k * S.card ^ 2 := by
  calc
    D.card * n = ∑ _ ∈ D, n := by simp
    _ ≤ ∑ d ∈ D, k * (reps S d).card := sum_le_sum h
    _ ≤ _ := by rw [← mul_sum]; gcongr; exact sum_reps_le S D

private lemma swap_counts {α β : Type*} (A : Finset α) (B : Finset β)
    (r : α → β → Prop) [DecidableRel r] :
    ∑ a ∈ A, (B.filter (r a)).card = ∑ b ∈ B, (A.filter fun a => r a b).card := by
  simp only [card_filter]
  rw [sum_comm]

private def row (A L : Finset ℤ) (t : ℤ) := A.filter fun x => x + t ∈ L

-- A common neighbor of x and z represents x-z as a difference of two labels.
private lemma common_le {A L : Finset ℤ} (x z : ℤ) :
    (A.filter fun t => x ∈ row A L t ∧ z ∈ row A L t).card ≤ (reps L (x - z)).card := by
  apply card_le_card_of_injOn (fun t => (x + t, z + t))
  · intro t ht
    obtain ⟨_, hx, hz⟩ := mem_filter.mp ht
    exact mem_filter.mpr ⟨mem_product.mpr ⟨(mem_filter.mp hx).2, (mem_filter.mp hz).2⟩, by ring⟩
  · intro t _ s _ h
    exact add_left_cancel (Prod.mk.inj h).1

private def thinPairs (A L : Finset ℤ) (q n : ℕ) :=
  (A ×ˢ A).filter fun p => q * (reps L (p.1 - p.2)).card < n

private lemma thin_sum (A L : Finset ℤ) (q : ℕ) :
    q * ∑ t ∈ A, (thinPairs (row A L t) L q A.card).card ≤ A.card ^ 3 := by
  let B := thinPairs A L q A.card
  have hrow (t : ℤ) : thinPairs (row A L t) L q A.card =
      B.filter (fun p => p.1 ∈ row A L t ∧ p.2 ∈ row A L t) := by
    ext p
    simp only [B, thinPairs, row, mem_product, mem_filter]
    tauto
  simp_rw [hrow]
  rw [swap_counts A B, mul_sum]
  calc
    _ ≤ ∑ _ ∈ B, A.card := by
      refine sum_le_sum fun p hp => ?_
      exact (Nat.mul_le_mul_left q (common_le p.1 p.2)).trans (mem_filter.mp hp).2.le
    _ ≤ _ := by
      have hB : B.card ≤ A.card * A.card := by
        simpa [B, thinPairs] using
          card_filter_le (A ×ˢ A) (fun p => q * (reps L (p.1 - p.2)).card < A.card)
      simpa [pow_succ] using Nat.mul_le_mul_right A.card hB

-- Choose a large neighborhood in which only a small fraction of pairs are thin.
private lemma exists_row {A L : Finset ℤ} {k : ℕ} (hn : 0 < A.card)
    (hd : A.card ^ 2 ≤ k * ∑ t ∈ A, (row A L t).card) :
    ∃ T ⊆ A, A.card ≤ 2 * k * T.card ∧
      8 * (thinPairs T L (64 * k ^ 2) A.card).card ≤ T.card ^ 2 := by
  let q := 64 * k ^ 2
  let bad t := (thinPairs (row A L t) L q A.card).card
  have hsum : ∑ t ∈ A, (2 * A.card ^ 2 + q * bad t) ≤
      ∑ t ∈ A, 4 * A.card * k * (row A L t).card := by
    rw [sum_add_distrib, sum_const, Nat.nsmul_eq_mul, ← mul_sum, ← mul_sum]
    have h := thin_sum A L q
    change q * ∑ t ∈ A, bad t ≤ _ at h
    nlinarith [Nat.mul_le_mul_left (4 * A.card) hd]
  obtain ⟨t, _, ht⟩ := exists_le_of_sum_le (card_pos.mp hn) hsum
  let T := row A L t
  have hT : A.card ≤ 2 * k * T.card := by
    apply Nat.le_of_mul_le_mul_left (c := 2 * A.card) _ (by positivity)
    change 2 * A.card * A.card ≤ 2 * A.card * (2 * k * (row A L t).card)
    nlinarith
  refine ⟨T, filter_subset .., hT, ?_⟩
  have hk : 0 < k := by by_contra! h; have := Nat.eq_zero_of_le_zero h; simp_all
  apply Nat.le_of_mul_le_mul_left (c := 8 * k ^ 2) _ (by positivity)
  change 2 * A.card ^ 2 + 64 * k ^ 2 * bad t ≤ 4 * A.card * k * T.card at ht
  change 8 * k ^ 2 * (8 * bad t) ≤ _
  nlinarith [Nat.mul_le_mul_right (4 * k * T.card) hT]

-- Remove vertices with too many thin partners. Any two remaining vertices have
-- at least half the neighborhood as common non-thin partners.
private lemma refine_row (T L : Finset ℤ) (q n : ℕ) (ht : 0 < T.card)
    (hb : 8 * (thinPairs T L q n).card ≤ T.card ^ 2) :
    ∃ X ⊆ T, T.card ≤ 2 * X.card ∧ ∀ x ∈ X, ∀ y ∈ X,
      T.card ≤ 2 * (T.filter fun z =>
        n ≤ q * (reps L (x - z)).card ∧ n ≤ q * (reps L (y - z)).card).card := by
  let bad x := T.filter fun z => q * (reps L (x - z)).card < n
  let X := T.filter fun x => 4 * (bad x).card ≤ T.card
  have hsum : ∑ x ∈ T, (bad x).card = (thinPairs T L q n).card := by
    simp only [thinPairs, bad, card_filter, sum_product]
  have hrem : (T \ X).card * T.card ≤ 4 * (thinPairs T L q n).card := by
    calc
      _ = ∑ _ ∈ T \ X, T.card := by simp
      _ ≤ ∑ x ∈ T \ X, 4 * (bad x).card := by
        apply sum_le_sum
        intro x hx
        obtain ⟨hxT, hxX⟩ := mem_sdiff.mp hx
        exact le_of_not_ge (fun h => hxX (mem_filter.mpr ⟨hxT, h⟩))
      _ ≤ _ := by
        rw [← mul_sum, ← hsum]
        exact Nat.mul_le_mul_left _ (sum_le_sum_of_subset sdiff_subset)
  have hTX : X ⊆ T := filter_subset ..
  have hpart := card_sdiff_add_card_eq_card hTX
  refine ⟨X, hTX, ?_, ?_⟩
  · apply Nat.le_of_mul_le_mul_left (c := T.card) _ ht
    nlinarith [congrArg (· * T.card) hpart]
  · intro x hx y hy
    have h₁ := (mem_filter.mp hx).2
    have h₂ := (mem_filter.mp hy).2
    have heq : (T.filter fun z =>
        n ≤ q * (reps L (x - z)).card ∧ n ≤ q * (reps L (y - z)).card) =
        T \ (bad x ∪ bad y) := by
      ext z
      simp [bad]
      tauto
    rw [heq]
    have := card_le_card_sdiff_add_card (s := T) (t := bad x ∪ bad y)
    have := card_union_le (bad x) (bad y)
    omega

-- Two popular differences with a common endpoint represent a difference in X-X.
private lemma small_difference_subset {A L : Finset ℤ} {k : ℕ}
    (hn : 0 < A.card) (hL : L.card ≤ A.card)
    (hd : A.card ^ 2 ≤ k * ∑ t ∈ A, (row A L t).card) :
    ∃ X ⊆ A, A.card ≤ 4 * k * X.card ∧
      (X - X).card ≤ (4 * k * (64 * k ^ 2)) ^ 2 * X.card := by
  let q := 64 * k ^ 2
  obtain ⟨T, hTA, ht, hb⟩ := exists_row hn hd
  have htpos : 0 < T.card := by
    by_contra! hz
    rw [Nat.eq_zero_of_le_zero hz, mul_zero] at ht
    omega
  obtain ⟨X, hXT, hx, hcommon⟩ := refine_row T L q A.card htpos hb
  have hnX : A.card ≤ 4 * k * X.card := by nlinarith [Nat.mul_le_mul_left (2 * k) hx]
  refine ⟨X, hXT.trans hTA, hnX, ?_⟩
  let P := (A - A).filter fun d => A.card ≤ q * (reps L d).card
  have hp : P.card ≤ q * A.card := by
    have h := popular_bound (S := L) (D := P) fun d hd => (mem_filter.mp hd).2
    apply Nat.le_of_mul_le_mul_right _ hn
    calc
      P.card * A.card ≤ q * L.card ^ 2 := h
      _ ≤ q * A.card ^ 2 := by gcongr
      _ = _ := by ring
  have hdiff (d : ℤ) (hd : d ∈ X - X) : T.card ≤ 2 * (reps P d).card := by
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_sub.mp hd
    apply (hcommon x hx y hy).trans
    apply Nat.mul_le_mul_left
    apply card_le_card_of_injOn (fun z => (x - z, y - z))
    · intro z hz
      obtain ⟨hz, hxz, hyz⟩ := mem_filter.mp hz
      refine mem_filter.mpr ⟨mem_product.mpr ⟨?_, ?_⟩, by ring⟩
      · exact mem_filter.mpr ⟨sub_mem_sub (hTA (hXT hx)) (hTA hz), hxz⟩
      · exact mem_filter.mpr ⟨sub_mem_sub (hTA (hXT hy)) (hTA hz), hyz⟩
    · intro z _ w _ he
      have := (Prod.mk.inj he).1
      omega
  have h := popular_bound hdiff
  have h' : (X - X).card ≤ 4 * k * q ^ 2 * A.card := by
    apply Nat.le_of_mul_le_mul_right _ htpos
    calc
      _ ≤ 2 * P.card ^ 2 := h
      _ ≤ 2 * (q * A.card) ^ 2 := by gcongr
      _ = 2 * q ^ 2 * A.card * A.card := by ring
      _ ≤ 2 * q ^ 2 * A.card * (2 * k * T.card) := by gcongr
      _ = _ := by ring
  calc
    _ ≤ 4 * k * q ^ 2 * (4 * k * X.card) := h'.trans (Nat.mul_le_mul_left _ hnX)
    _ = _ := by dsimp [q]; ring

private def overlap (B : Finset ℤ) (d : ℤ) := B.filter fun x => x + d ∈ B

private lemma overlap_flip (B : Finset ℤ) (d : ℤ) :
    (overlap B d).card ≤ (overlap B (-d)).card := by
  apply card_le_card_of_injOn (· + d)
  · intro x hx
    obtain ⟨hx, hx'⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨hx', by simpa⟩
  · exact (add_left_injective d).injOn

private lemma sum_overlap {X B : Finset ℤ} (hBX : B ⊆ X) :
    ∑ d ∈ X - X, (overlap B d).card = B.card ^ 2 := by
  unfold overlap
  rw [swap_counts (X - X) B (fun d x => x + d ∈ B)]
  calc
    _ = ∑ _ ∈ B, B.card := by
      apply sum_congr rfl
      intro x hx
      apply card_bij' (fun d _ => x + d) (fun y _ => y - x)
      · exact fun _ hd => (mem_filter.mp hd).2
      · exact fun y hy => mem_filter.mpr ⟨sub_mem_sub (hBX hy) (hBX hx), by simpa⟩
      · simp
      · simp
    _ = _ := by simp [sq]

-- Inside a set of small difference set, a relatively large subset overlaps one of
-- its nonzero translates in another relatively large subset.
private lemma positive_overlap {X B : Finset ℤ} {C K : ℕ} (hBX : B ⊆ X)
    (hB : 2 ≤ B.card) (hx : X.card ≤ C * B.card) (hK : (X - X).card ≤ K * X.card) :
    ∃ d : ℤ, 0 < d ∧ X.card ≤ (2 * K * C ^ 2) * (overlap B d).card := by
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hB
  let D := (X - X).erase 0
  have hD : D.Nonempty :=
    ⟨a - b, mem_erase.mpr ⟨sub_ne_zero.mpr hab, sub_mem_sub (hBX ha) (hBX hb)⟩⟩
  have hz : (0 : ℤ) ∈ X - X := by simpa using sub_mem_sub (hBX ha) (hBX ha)
  have hs := sum_erase_add (s := X - X) (fun d => (overlap B d).card) hz
  rw [sum_overlap hBX] at hs
  have hov : overlap B 0 = B := by ext; simp [overlap]
  rw [hov] at hs
  have hbs : B.card ^ 2 ≤ 2 * ∑ d ∈ D, (overlap B d).card := by
    dsimp [D]
    nlinarith [Nat.mul_le_mul_right B.card hB]
  have hd : D.card ≤ K * X.card := (card_le_card (erase_subset ..)).trans hK
  have havg : ∑ _ ∈ D, X.card ≤ ∑ d ∈ D, (2 * K * C ^ 2) * (overlap B d).card := by
    rw [sum_const, Nat.nsmul_eq_mul, ← mul_sum]
    calc
      _ ≤ K * X.card * X.card := by gcongr
      _ ≤ K * (C * B.card) * (C * B.card) := by gcongr
      _ = K * C ^ 2 * B.card ^ 2 := by ring
      _ ≤ K * C ^ 2 * (2 * ∑ d ∈ D, (overlap B d).card) := by gcongr
      _ = _ := by ring
  obtain ⟨d, hd, hsize⟩ := exists_le_of_sum_le hD havg
  rcases lt_or_gt_of_ne (mem_erase.mp hd).1 with h | h
  · exact ⟨-d, by omega, hsize.trans (Nat.mul_le_mul_left _ (overlap_flip B d))⟩
  · exact ⟨d, h, hsize⟩

-- Iterating positive overlaps builds a cube, with all its edge lengths positive.
private lemma binary_cube (m K C : ℕ) :
    ∃ M : ℕ, ∀ X B : Finset ℤ, M ≤ X.card → B ⊆ X → X.card ≤ C * B.card →
      (X - X).card ≤ K * X.card →
      ∃ (a : ℤ) (d : Fin m → ℤ), (∀ i, 0 < d i) ∧
        ∀ w : Fin m → ℤ, (∀ i, w i = 0 ∨ w i = 1) → a + ∑ i, w i * d i ∈ B := by
  induction m generalizing C with
  | zero =>
    refine ⟨1, fun X B hM _ hsize _ => ?_⟩
    have hpos : 0 < B.card := by
      by_contra! hz
      rw [Nat.eq_zero_of_le_zero hz, mul_zero] at hsize
      omega
    obtain ⟨a, ha⟩ := card_pos.mp hpos
    exact ⟨a, Fin.elim0, (fun i => i.elim0), fun _ _ => by simpa⟩
  | succ m ih =>
    obtain ⟨M, hM⟩ := ih (2 * K * C ^ 2)
    refine ⟨max M (C + 1), fun X B hmax hBX hsize hK => ?_⟩
    have hB : 2 ≤ B.card := by
      have hlt := (le_max_right M (C + 1)).trans hmax
      by_contra! hz
      have := Nat.mul_le_mul_left C (show B.card ≤ 1 by omega)
      omega
    obtain ⟨s, hs, hBs⟩ := positive_overlap hBX hB hsize hK
    obtain ⟨a, d, hd, hw⟩ := hM X (overlap B s) ((le_max_left ..).trans hmax)
      ((filter_subset ..).trans hBX) hBs hK
    refine ⟨a, Fin.cons s d, Fin.forall_fin_succ.mpr ⟨hs, hd⟩, fun w h => ?_⟩
    have hmem := mem_filter.mp (hw (fun i => w i.succ) fun i => h i.succ)
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rcases h 0 with he | he
    · simpa [he] using hmem.1
    · simpa [he, add_assoc, add_left_comm, add_comm] using hmem.2

private def weight {m : ℕ} (d : Fin m → ℤ) (w : Fin m → Fin 4) : ℤ :=
  ∑ i, (w i : ℤ) * d i

-- Each word with letters 0,1,2,3 is a sum of three binary words.
private lemma weight_mem {m : ℕ} {X : Finset ℤ} {a : ℤ} {d : Fin m → ℤ}
    (hw : ∀ w : Fin m → ℤ, (∀ i, w i = 0 ∨ w i = 1) → a + ∑ i, w i * d i ∈ X)
    (w : Fin m → Fin 4) : 3 * a + weight d w ∈ 3 • X := by
  let bit (j : ℕ) (i : Fin m) : ℤ := if j < (w i).val then 1 else 0
  have hbit (j : ℕ) := hw (bit j) fun i => by dsimp [bit]; split <;> simp
  have hval (i : Fin m) : (w i : ℤ) = bit 0 i + bit 1 i + bit 2 i := by
    dsimp [bit]
    have := (w i).isLt
    split_ifs <;> omega
  have heq : 3 * a + weight d w =
      (a + ∑ i, bit 0 i * d i) + (a + ∑ i, bit 1 i * d i) + (a + ∑ i, bit 2 i * d i) := by
    simp_rw [weight, hval, add_mul, sum_add_distrib]
    ring
  rw [heq, show 3 • X = X + X + X by rw [three_nsmul]; abel]
  exact add_mem_add (add_mem_add (hbit 0) (hbit 1)) (hbit 2)

private lemma weight_line {m : ℕ} (d : Fin m → ℤ) (hd : ∀ i, 0 < d i)
    (l : Combinatorics.Line (Fin 4) (Fin m)) :
    ∃ b s : ℤ, 0 < s ∧ ∀ j : Fin 4, weight d (l j) = b + (j : ℤ) * s := by
  let W := univ.filter fun i => l.idxFun i = none
  obtain ⟨i, hi⟩ := l.proper
  have hW : W.Nonempty := ⟨i, by simp [W, hi]⟩
  refine ⟨∑ i ∈ Wᶜ, ((l 0 i : Fin 4) : ℤ) * d i, ∑ i ∈ W, d i,
    sum_pos (fun i _ => hd i) hW, fun j => ?_⟩
  rw [weight, ← sum_add_sum_compl W, mul_sum, add_comm]
  congr 1
  · apply sum_congr rfl
    intro i hi
    obtain ⟨x, hx⟩ := Option.ne_none_iff_exists.mp (show l.idxFun i ≠ none by simpa [W] using hi)
    simp [Combinatorics.Line.coe_apply, ← hx]
  · apply sum_congr rfl
    intro i hi
    rw [l.apply_none j i (mem_filter.mp hi).2]

-- Average translates of the four-letter cube. Its values lie in 3X, so X-3X
-- contains every relevant translation, independently of the cube dimension.
private lemma dense_translate {m : ℕ} (X : Finset ℤ) (w : (Fin m → Fin 4) → ℤ)
    (hw : ∀ u, w u ∈ 3 • X) (hX : X.Nonempty) (K : ℕ)
    (hK : (X - 3 • X).card ≤ K * X.card) :
    ∃ t : ℤ, 4 ^ m ≤ K * (univ.filter fun u => t + w u ∈ X).card := by
  let T := X - 3 • X
  have hT : T.Nonempty := by
    obtain ⟨x, hx⟩ := hX
    exact ⟨_, sub_mem_sub hx (hw (fun _ => 0))⟩
  have hcount (u : Fin m → Fin 4) : (T.filter fun t => t + w u ∈ X).card = X.card := by
    apply card_bij' (fun t _ => t + w u) (fun x _ => x - w u)
    · exact fun _ ht => (mem_filter.mp ht).2
    · exact fun x hx => mem_filter.mpr ⟨sub_mem_sub hx (hw u), by simpa⟩
    · simp
    · simp
  have hsum : ∑ _ ∈ T, 4 ^ m ≤ ∑ t ∈ T, K * (univ.filter fun u => t + w u ∈ X).card := by
    rw [← mul_sum, swap_counts T univ (fun t u => t + w u ∈ X)]
    simp_rw [hcount]
    simpa [mul_assoc, mul_comm, mul_left_comm, T] using Nat.mul_le_mul_right (4 ^ m) hK
  obtain ⟨t, _, ht⟩ := exists_le_of_sum_le hT hsum
  exact ⟨t, ht⟩

private lemma small_difference_four (K : ℕ) (hKpos : 0 < K) :
    ∃ M : ℕ, ∀ X : Finset ℤ, M ≤ X.card → (X - X).card ≤ K * X.card →
      ∃ b s : ℤ, 0 < s ∧ ∀ j : Fin 4, b + (j : ℤ) * s ∈ X := by
  obtain ⟨m, hline⟩ := MathlibExt.Combinatorics.DensityHalesJewettWanted.density_hales_jewett
    4 (by decide) ((K : ℝ) ^ 4)⁻¹ (by positivity)
  obtain ⟨M, hcube⟩ := binary_cube m K 1
  refine ⟨max M 1, fun X hM hK => ?_⟩
  have hx : 0 < X.card := (le_max_right M 1).trans hM
  obtain ⟨a, d, hd, hw⟩ := hcube X X ((le_max_left ..).trans hM) Subset.rfl (by simp) hK
  have hbound : (X - 3 • X).card ≤ K ^ 4 * X.card := by
    have hr : ((X - X).card : ℚ≥0) / X.card ≤ K := by
      rw [div_le_iff₀ (by exact_mod_cast hx)]
      exact_mod_cast hK
    have hp := pluennecke_ruzsa_inequality_nsmul_sub_nsmul_sub (card_pos.mp hx) X 1 3
    simp only [one_nsmul] at hp
    exact_mod_cast hp.trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hr 4) (by positivity))
  obtain ⟨t, ht⟩ := dense_translate X _ (weight_mem hw) (card_pos.mp hx) _ hbound
  let U := univ.filter fun w => t + (3 * a + weight d w) ∈ X
  have hden : ((K : ℝ) ^ 4)⁻¹ * 4 ^ m ≤ U.card := by
    rw [inv_mul_le_iff₀ (by positivity)]
    exact_mod_cast ht
  obtain ⟨l, hl⟩ := hline U hden
  obtain ⟨b, s, hs, he⟩ := weight_line d hd l
  refine ⟨t + 3 * a + b, s, hs, fun j => ?_⟩
  have h := (mem_filter.mp (hl j)).2
  simpa only [he, add_assoc] using h

private def intSet (A : Finset ℕ) : Finset ℤ := A.image (fun a : ℕ => (a : ℤ))

private lemma card_intSet (A : Finset ℕ) : (intSet A).card = A.card :=
  card_image_of_injective _ Nat.cast_injective

-- Send a progression to its two endpoints. Their sum is twice the middle term.
private lemma count_edges (A : Finset ℕ) :
    apCount A 3 ≤ ∑ t ∈ intSet A, (row (intSet A) ((intSet A).image (2 * ·)) t).card := by
  let S := intSet A
  let L := S.image (2 * ·)
  let E := (S ×ˢ S).filter fun p => p.2 + p.1 ∈ L
  have hE : E.card = ∑ t ∈ S, (row S L t).card := by
    simp only [E, row, card_filter, sum_product]
  rw [← hE]
  apply card_le_card_of_injOn (fun p : ℕ × ℕ => ((p.1 : ℤ), (p.1 : ℤ) + 2 * p.2))
  · intro p hp
    obtain ⟨hp, hall⟩ := mem_filter.mp hp
    have h₀ := (mem_product.mp hp).1
    have h₁ := hall 1 (by decide)
    have h₂ := hall 2 (by decide)
    simp only [one_mul] at h₁
    refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_image_of_mem _ h₀, ?_⟩, ?_⟩
    · exact_mod_cast (show ((p.1 + 2 * p.2 : ℕ) : ℤ) ∈ S from mem_image_of_mem _ h₂)
    · refine mem_image.mpr ⟨_, mem_image_of_mem (fun a : ℕ => (a : ℤ)) h₁, ?_⟩
      push_cast
      ring
  · rintro ⟨a, d⟩ _ ⟨b, e⟩ _ h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    apply Prod.ext <;> dsimp at * <;> omega

private lemma force_four (k : ℕ) (hk : 0 < k) :
    ∃ M : ℕ, ∀ A : Finset ℕ, M ≤ A.card → A.card ^ 2 ≤ k * apCount A 3 → HasAP A 4 := by
  let K := (4 * k * (64 * k ^ 2)) ^ 2
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨M, hM⟩ := small_difference_four K hK
  refine ⟨4 * k * M + 1, fun A hA hcount => ?_⟩
  let S := intSet A
  have hS : S.card = A.card := card_intSet A
  let L := S.image (2 * ·)
  have hd : S.card ^ 2 ≤ k * ∑ t ∈ S, (row S L t).card := by
    rw [hS]
    exact hcount.trans (Nat.mul_le_mul_left k (count_edges A))
  obtain ⟨X, hXS, hX, hdiff⟩ :=
    small_difference_subset (by omega) (card_image_le : L.card ≤ S.card) hd
  have hMX : M ≤ X.card := Nat.le_of_mul_le_mul_left (by omega) (by positivity : 0 < 4 * k)
  obtain ⟨b, s, hs, hfour⟩ := hM X hMX hdiff
  have h0 := hXS (hfour 0)
  obtain ⟨a, _, ha⟩ := mem_image.mp h0
  simp only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero] at ha
  refine ⟨a, s.toNat, by omega, fun i hi => ?_⟩
  obtain ⟨v, hv, he⟩ := mem_image.mp (hXS (hfour ⟨i, hi⟩))
  have hv' : (v : ℤ) = (a : ℤ) + (i : ℤ) * (s.toNat : ℤ) := by
    rw [Int.toNat_of_nonneg hs.le, ha]
    exact he
  rwa [show a + i * s.toNat = v by exact_mod_cast hv'.symm]

/--
**Erdős Problem 179: $F_3(N, 4) = o(N^2)$.** As $N \to \infty$ over the natural numbers,
$F_3(N, 4) / N^2 \to 0$, that is, $F_3(N, 4) = o(N^2)$, where $F_3(N, 4)$ is the least natural
number $m$ such that every $N$-element set $A \subseteq \mathbb{N}$ containing at least $m$
three-term arithmetic progressions $a, a + d, a + 2d$ with $d \ge 1$ contains a $4$-term
arithmetic progression.

Write $F_k(N, \ell)$ for the same threshold with $k$-term progressions in place of three-term ones
and $\ell$-term progressions in place of $4$-term ones. Fox and Pohoata bound $F_k(N, \ell)$ above
by $(r_\ell(N) / N)^{O(1)} N^2$, where $r_\ell(N)$ is the largest size of a subset of
$\{1, \dots, N\}$ without $\ell$-term progressions; since $r_\ell(N) = o(N)$ by Szemerédi's
theorem, this bound is $o(N^2)$. erdosproblems.com/179 records
$F_k(N, \ell) \le N^2 / (\log \log N)^{C_\ell}$ for a constant $C_\ell$ depending only on $\ell$.

Source: T.
F. Bloom, Erdős Problems, Problem #179, https://www.erdosproblems.com/179 (status PROVED);
resolution: J. Fox and C. Pohoata, Sets without k-term progressions can have many shorter
progressions, Random Structures Algorithms 58 (2021), 383-389, arXiv:1908.09905, main theorem: for
all k > s ≥ 3, log f_{s,k}(n) / log n → 2, where f_{s,k}(n) = F_s(n, k) - 1 is the largest number of
s-term progressions in an n-set with no k-term progression; erdosproblems.com/179: F_k(N, ℓ) ≤ N² /
(log log N)^{C_ℓ}, https://arxiv.org/abs/1908.09905.
-/
public theorem threeAPThresholdForFourAPLittleO_holds : threeAPThresholdForFourAPLittleO := by
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / ε)
  have hk' : 2 < (k : ℝ) * ε := (div_lt_iff₀ hε).mp hk
  have hkpos : 0 < k := by
    by_contra! hz
    rw [Nat.eq_zero_of_le_zero hz] at hk'
    norm_num at hk'
  obtain ⟨M, hM⟩ := force_four k hkpos
  filter_upwards [Filter.eventually_ge_atTop (max M k)] with N hN
  have hth : apThreshold 3 4 N ≤ N ^ 2 / k + 1 := by
    apply Nat.sInf_le
    intro A hAN hc
    apply hM A (hAN ▸ (le_max_left M k).trans hN)
    rw [hAN]
    exact ((Nat.div_lt_iff_lt_mul hkpos).mp (by omega : N ^ 2 / k < apCount A 3)).le.trans_eq
      (Nat.mul_comm ..)
  have hkN := (le_max_right M k).trans hN
  have hkN₂ : k ≤ N ^ 2 := by nlinarith [Nat.le_mul_self N]
  have hscaled : k * apThreshold 3 4 N ≤ 2 * N ^ 2 := by
    have := Nat.mul_le_mul_left k hth
    have := Nat.div_mul_le_self (N ^ 2) k
    nlinarith
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  apply le_of_mul_le_mul_left (a := (k : ℝ)) _ (by exact_mod_cast hkpos)
  calc
    _ ≤ 2 * (N : ℝ) ^ 2 := by exact_mod_cast hscaled
    _ ≤ (k * ε) * (N : ℝ) ^ 2 := by gcongr
    _ = _ := by ring

end MathlibExt.Combinatorics.ManyThreeTermProgressionsErdosProblem179Wanted
