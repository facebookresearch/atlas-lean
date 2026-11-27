/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Distinct consecutive sums in increasing sequences

We prove the positive answer to Erdős Problem 356 by averaging over a finite family of
increasing sequences. Each sequence consists of the successive differences of a quadratic
function with a rounded linear perturbation on its second half. For each gap between right
endpoints, we bound both the number of possible left endpoints and the number of slopes
giving the same sum. Averaging gives a slope with at most `28 * m ^ 2` equal pairs among
`m ^ 2` intervals. Cauchy–Schwarz then gives at least `m ^ 2 / 28` distinct sums.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.IncreasingSequenceConsecutiveSumsErdosProblem356Wanted

/-- **Consecutive sums.** Let $k \in \mathbb{N}$ and let $a_0, \dots, a_{k-1}$ be natural
numbers. The consecutive sums of $a$ form the finite set of natural numbers
$a_u + a_{u+1} + \dots + a_v$ for indices $0 \le u \le v \le k - 1$. -/
def consecutiveSums {k : ℕ} (a : Fin k → ℕ) : Finset ℕ :=
  ((Finset.univ : Finset (Fin k × Fin k)).filter fun p => p.1 ≤ p.2).image
    fun p => ∑ i ∈ Finset.Icc p.1 p.2, a i

/-- **Erdős Problem 356.** The proposition that there is a real number $c > 0$ such that for all
sufficiently large $n \in \mathbb{N}$ there exist $k \in \mathbb{N}$ and natural numbers
$a_0 < a_1 < \dots < a_{k-1}$ with $1 \le a_i \le n$ for every $i$, whose set of consecutive sums
$a_u + a_{u+1} + \dots + a_v$ (for $u \le v$) has at least $c n^2$ elements. -/
def manyDistinctConsecutiveSums : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, ∃ k : ℕ, ∃ a : Fin k → ℕ, StrictMono a ∧
    (∀ i, 1 ≤ a i ∧ a i ≤ n) ∧ c * (n : ℝ) ^ 2 ≤ (consecutiveSums a).card

open Finset

private def quadratic (m i : ℕ) : ℕ := i * i + m * i

private def tilt (m t i : ℕ) : ℕ := t * (i - m) / m

private def prefixSum (m t i : ℕ) : ℕ := quadratic m i + tilt m t i

private lemma tilt_mono (m t : ℕ) : Monotone (tilt m t) := by
  intro i j hij
  exact Nat.div_le_div_right (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hij _))

private lemma prefix_mono (m t : ℕ) : Monotone (prefixSum m t) := by
  intro i j hij
  unfold prefixSum quadratic
  gcongr
  exact tilt_mono m t hij

private def step (m t i : ℕ) : ℕ := prefixSum m t (i + 1) - prefixSum m t i

private lemma step_eq (m t i : ℕ) :
    step m t i = m + 2 * i + 1 + (tilt m t (i + 1) - tilt m t i) := by
  have h : tilt m t i ≤ tilt m t (i + 1) := tilt_mono m t i.le_succ
  unfold step prefixSum quadratic
  rw [show (i + 1) * (i + 1) + m * (i + 1) = i * i + m * i + (m + 2 * i + 1) by ring]
  omega

private lemma tilt_step (m t i : ℕ) (hm : 0 < m) (hi : m ≤ i) :
    t / m ≤ tilt m t (i + 1) - tilt m t i ∧
      tilt m t (i + 1) - tilt m t i ≤ t / m + 1 := by
  unfold tilt
  rw [show i + 1 - m = (i - m) + 1 by omega, Nat.mul_succ, Nat.add_div hm]
  split <;> simp [Nat.add_assoc]

private lemma step_strictMono (m t : ℕ) (hm : 0 < m) : StrictMono (step m t) := by
  apply strictMono_nat_of_lt_succ
  intro i
  rw [step_eq, step_eq]
  by_cases hi : m ≤ i
  · have h := tilt_step m t i hm hi
    have h' := tilt_step m t (i + 1) hm (by omega)
    omega
  · have hz : tilt m t (i + 1) = 0 := by simp [tilt, Nat.sub_eq_zero_of_le (by omega : i + 1 ≤ m)]
    omega

private lemma step_bounds (m t i : ℕ) (hm : 0 < m) (ht : t < m * m) (hi : i < 2 * m) :
    1 ≤ step m t i ∧ step m t i ≤ 6 * m := by
  rw [step_eq]
  have hdiv := (Nat.div_lt_iff_lt_mul hm).2 ht
  by_cases h : m ≤ i
  · have hs := tilt_step m t i hm h
    omega
  · simp [tilt, Nat.sub_eq_zero_of_le (by omega : i + 1 ≤ m)]
    omega

-- Intervals crossing the midpoint are indexed by two independent endpoints.
private def value (m t i j : ℕ) : ℕ := prefixSum m t (m + j) - prefixSum m t i

private lemma value_eq (m t i j : ℕ) (hi : i ≤ m) :
    value m t i j + quadratic m i = quadratic m (m + j) + t * j / m := by
  have h := Nat.sub_add_cancel (prefix_mono m t (show i ≤ m + j by omega))
  simpa [value, prefixSum, tilt, Nat.sub_eq_zero_of_le hi] using h

private lemma value_mem {m t i j : ℕ} (hi : i < m) (hj : j < m) :
    value m t i j ∈ consecutiveSums (fun x : Fin (2 * m) => step m t x) := by
  let u : Fin (2 * m) := ⟨i, by omega⟩
  let v : Fin (2 * m) := ⟨m + j - 1, by omega⟩
  have huv : u ≤ v := by change i ≤ m + j - 1; omega
  refine mem_image.mpr ⟨(u, v), by simpa using huv, ?_⟩
  change ∑ x ∈ Icc u v, step m t (Fin.valEmbedding x) = _
  rw [← sum_map (Icc u v) Fin.valEmbedding (step m t), Fin.map_valEmbedding_Icc]
  change ∑ x ∈ Icc i (m + j - 1), step m t x = _
  rw [← Ico_add_one_right_eq_Icc, Nat.sub_add_cancel (by omega : 1 ≤ m + j)]
  have tel : ∀ b, i ≤ b → (∑ x ∈ Ico i b, step m t x) + prefixSum m t i = prefixSum m t b := by
    intro b hib
    induction b, hib using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      rw [sum_Ico_succ_top hk, add_right_comm, ih, step,
        Nat.add_sub_of_le (prefix_mono m t k.le_succ)]
  unfold value
  have := tel (m + j) (by omega)
  omega

-- For a fixed gap d between right endpoints, the unrounded change in the quadratic
-- part is d * (3*m + 2*j + d). Rounding the change in the linear part costs at most one.
private lemma collision_bounds {m t i k j d : ℕ} (hm : 0 < m) (hi : i < m) (hk : k < m)
    (h : value m t i j = value m t k (j + d)) :
    let b := quadratic m i + d * (3 * m + 2 * j + d)
    b + t * d / m ≤ quadratic m k ∧ quadratic m k ≤ b + t * d / m + 1 := by
  have h₁ := value_eq m t i j hi.le
  have h₂ := value_eq m t k (j + d) hk.le
  rw [← h, Nat.mul_add, Nat.add_div hm] at h₂
  rw [show quadratic m (m + (j + d)) = quadratic m (m + j) + d * (3 * m + 2 * j + d)
      by unfold quadratic; ring] at h₂
  dsimp only
  split at h₂ <;> omega

private lemma left_endpoint_mem {m t i k j d : ℕ} (hm : 0 < m) (ht : t < m * m)
    (hi : i < m) (hk : k < m) (hd : 0 < d) (hj : j + d < m)
    (h : value m t i j = value m t k (j + d)) : k ∈ Icc i (i + 8 * d) := by
  obtain ⟨hlo, hhi⟩ := collision_bounds hm hi hk h
  have hdiv : t * d / m ≤ m * d := by
    apply Nat.div_le_of_le_mul
    calc
      t * d ≤ (m * m) * d := Nat.mul_le_mul_right _ ht.le
      _ = _ := by ring
  have hbase : d * (3 * m + 2 * j + d) ≤ d * (6 * m) :=
    Nat.mul_le_mul_left _ (by omega)
  have hik : i ≤ k := by
    by_contra! hki
    have hs := Nat.mul_self_le_mul_self hki.le
    unfold quadratic at hlo
    apply (Nat.not_lt_of_ge hlo)
    exact (Nat.add_lt_add_of_le_of_lt hs (Nat.mul_lt_mul_of_pos_left hki hm)).trans_le
      ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
  refine mem_Icc.mpr ⟨hik, ?_⟩
  by_contra! hki
  have hs := Nat.mul_self_le_mul_self hik
  unfold quadratic at hhi
  nlinarith [Nat.mul_lt_mul_of_pos_left hki hm, Nat.mul_pos hm hd]

private lemma slope_separation {m t u i k j d : ℕ} (hm : 0 < m) (hi : i < m) (hk : k < m)
    (hd : 0 < d) (htu : t ≤ u) (ht : value m t i j = value m t k (j + d))
    (hu : value m u i j = value m u k (j + d)) : u ≤ t + 2 * m / d := by
  obtain ⟨_, ht'⟩ := collision_bounds hm hi hk ht
  obtain ⟨hu', _⟩ := collision_bounds hm hi hk hu
  have hq : u * d / m ≤ t * d / m + 1 := by omega
  have h₁ := Nat.mul_le_mul_right m hq
  have h₂ := Nat.div_mul_le_self (t * d) m
  have h₃ := Nat.lt_mul_div_succ (u * d) hm
  have hdiff : (u - t) * d ≤ 2 * m := by
    rw [Nat.sub_mul]
    have : u * d ≤ t * d + 2 * m := by nlinarith
    omega
  have := (Nat.le_div_iff_mul_le hd).2 hdiff
  omega

private def slopes (m i k j l : ℕ) : Finset ℕ :=
  (range (m * m)).filter fun t => value m t i j = value m t k l

private lemma slopes_card {m i k j d : ℕ} (hm : 0 < m) (hi : i < m) (hk : k < m) (hd : 0 < d) :
    (slopes m i k j (j + d)).card ≤ 2 * m / d + 1 := by
  let s := slopes m i k j (j + d)
  change s.card ≤ _
  obtain hs | hs := s.eq_empty_or_nonempty
  · simp [hs]
  let t := s.min' hs
  have ht : t ∈ s := s.min'_mem hs
  have hsub : s ⊆ Icc t (t + 2 * m / d) := by
    intro u hu
    have htu := s.min'_le u hu
    exact mem_Icc.mpr ⟨htu, slope_separation hm hi hk hd htu
      (mem_filter.mp ht).2 (mem_filter.mp hu).2⟩
  simpa [Nat.card_Icc, Nat.add_assoc] using card_le_card hsub

private lemma collision_row {m i j d : ℕ} (hm : 0 < m) (hi : i < m) (hd : 0 < d)
    (hj : j + d < m) : (∑ k ∈ range m, (slopes m i k j (j + d)).card) ≤ 27 * m := by
  let s := (range m).filter fun k => (slopes m i k j (j + d)).Nonempty
  have hs : s ⊆ Icc i (i + 8 * d) := by
    intro k hk
    obtain ⟨hk, t, ht⟩ := mem_filter.mp hk
    obtain ⟨ht, heq⟩ := mem_filter.mp ht
    exact left_endpoint_mem hm (mem_range.mp ht) hi (mem_range.mp hk) hd hj heq
  calc
    _ = ∑ k ∈ s, (slopes m i k j (j + d)).card := by
      symm
      apply sum_subset (filter_subset _ _)
      intro k hk hn
      simpa [s, hk] using hn
    _ ≤ s.card * (2 * m / d + 1) := by
      simpa using s.sum_le_card_nsmul (fun k => (slopes m i k j (j + d)).card) _ (fun k hk =>
        slopes_card hm hi (mem_range.mp (mem_filter.mp hk).1) hd)
    _ ≤ (9 * d) * (2 * m / d + 1) := by
      apply Nat.mul_le_mul_right
      have := card_le_card hs
      simp [Nat.card_Icc] at this
      omega
    _ ≤ 27 * m := by nlinarith [Nat.div_mul_le_self (2 * m) d]

private def blockCount (m j l : ℕ) : ℕ :=
  ∑ i ∈ range m, ∑ k ∈ range m, (slopes m i k j l).card

private lemma blockCount_comm (m j l : ℕ) : blockCount m j l = blockCount m l j := by
  unfold blockCount
  rw [sum_comm]
  simp only [slopes, eq_comm]

private lemma blockCount_off_diag {m j l : ℕ} (hm : 0 < m) (hj : j < m) (hl : l < m)
    (hne : j ≠ l) : blockCount m j l ≤ 27 * m * m := by
  wlog h : j < l generalizing j l
  · rw [blockCount_comm]
    exact this hl hj hne.symm (by omega)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h.le
  simpa [blockCount, mul_comm, mul_left_comm, mul_assoc] using
    (range m).sum_le_card_nsmul (fun i => ∑ k ∈ range m, (slopes m i k j (j + d)).card)
      (27 * m) (fun i hi => collision_row hm (mem_range.mp hi) (by omega) hl)

private lemma blockCount_diag (m j : ℕ) (hm : 0 < m) : blockCount m j j = m ^ 3 := by
  have hmono : StrictMono (quadratic m) := by
    intro a b hab
    exact Nat.add_lt_add_of_le_of_lt (Nat.mul_self_le_mul_self hab.le)
      (Nat.mul_lt_mul_of_pos_left hab hm)
  have hinj {t i k : ℕ} (hi : i < m) (hk : k < m) (h : value m t i j = value m t k j) :
      i = k := by
    apply hmono.injective
    have := value_eq m t i j hi.le
    have := value_eq m t k j hk.le
    omega
  unfold blockCount
  calc
    _ = ∑ i ∈ range m, (m * m) := by
      apply sum_congr rfl
      intro i hi
      rw [sum_eq_single_of_mem i hi]
      · simp [slopes]
      · intro k hk hki
        have h t : value m t i j ≠ value m t k j := fun e =>
          hki (hinj (mem_range.mp hi) (mem_range.mp hk) e).symm
        simp [slopes, h]
    _ = _ := by simp; ring

private lemma total_blocks (m : ℕ) (hm : 0 < m) :
    (∑ j ∈ range m, ∑ l ∈ range m, blockCount m j l) ≤ 28 * m ^ 4 := by
  calc
    _ ≤ ∑ j ∈ range m, ∑ l ∈ range m, (27 * m * m + if l = j then m ^ 3 else 0) := by
      apply sum_le_sum
      intro j hj
      apply sum_le_sum
      intro l hl
      by_cases heq : l = j
      · simp [heq, blockCount_diag m j hm]
      · simpa [heq] using blockCount_off_diag hm (mem_range.mp hj) (mem_range.mp hl) (Ne.symm heq)
    _ = _ := by
      simp only [sum_add_distrib, sum_const, card_range, smul_eq_mul, sum_ite_eq', mem_range]
      rw [sum_ite_of_true fun _ hj => mem_range.mp hj]
      simp
      ring

private def endpoints (m : ℕ) := range m ×ˢ range m

private def intervalValue (m t : ℕ) (p : ℕ × ℕ) := value m t p.2 p.1

private def collisions (m t : ℕ) : ℕ :=
  ∑ p ∈ endpoints m, ∑ q ∈ endpoints m,
    if intervalValue m t p = intervalValue m t q then 1 else 0

private lemma exists_few_collisions (m : ℕ) (hm : 0 < m) :
    ∃ t ∈ range (m * m), collisions m t ≤ 28 * m ^ 2 := by
  apply exists_le_of_sum_le (nonempty_range_iff.mpr (Nat.mul_ne_zero hm.ne' hm.ne'))
  calc
    _ = ∑ j ∈ range m, ∑ l ∈ range m, blockCount m j l := by
      simp only [collisions, endpoints, sum_product, intervalValue, blockCount, slopes, card_filter]
      simp_rw [sum_comm (s := range (m * m)) (t := range m)]
      exact sum_congr rfl fun j _ => sum_comm
    _ ≤ _ := by simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using total_blocks m hm

-- Cauchy–Schwarz for the sizes of the fibers of the interval-sum map.
private lemma card_le_image_mul_collisions (m t : ℕ) :
    (m * m) ^ 2 ≤ ((endpoints m).image (intervalValue m t)).card * collisions m t := by
  let s := endpoints m
  let f := intervalValue m t
  let freq := fun v => (s.filter fun p => f p = v).card
  have hc : m * m = ∑ v ∈ s.image f, freq v := by
    simpa only [freq, s, endpoints, card_product, card_range] using card_eq_sum_card_image f s
  have he : (∑ v ∈ s.image f, freq v ^ 2) = collisions m t := by
    calc
      _ = ∑ v ∈ s.image f, ∑ _p ∈ s.filter (fun p => f p = v), freq v := by simp [freq, sq]
      _ = ∑ p ∈ s, freq (f p) := sum_fiberwise_of_maps_to' (fun p hp => mem_image_of_mem f hp) freq
      _ = _ := by simp only [collisions, freq, s, f, card_filter, eq_comm]
  calc
    _ = (∑ v ∈ s.image f, freq v) ^ 2 := congrArg (· ^ 2) hc
    _ ≤ (s.image f).card * ∑ v ∈ s.image f, freq v ^ 2 := by
      simpa using sum_mul_sq_le_sq_mul_sq (s.image f) (fun _ => (1 : ℕ)) freq
    _ = _ := by rw [he]

/--
**Erdős Problem 356 has a positive answer.** There is a real number $c > 0$ such that for all
sufficiently large $n \in \mathbb{N}$ there exist $k \in \mathbb{N}$ and natural numbers
$a_0 < a_1 < \dots < a_{k-1}$ with $1 \le a_i \le n$ for every $i$, whose set of consecutive sums
$a_u + a_{u+1} + \dots + a_v$ (for $u \le v$) has at least $c n^2$ elements.

Source: T. F. Bloom,
Erdős Problems, Problem #356, https://www.erdosproblems.com/356 (status PROVED (LEAN)); resolution:
A. Beker, On a problem of Erdős and Graham about consecutive sums in strictly increasing sequences,
arXiv:2311.10087 (2023), erdosproblems.com/356: the original problem was solved in the affirmative
by Beker, https://arxiv.org/abs/2311.10087.
-/
public theorem manyDistinctConsecutiveSums_holds : manyDistinctConsecutiveSums := by
  refine ⟨1 / 4032, by norm_num, Filter.eventually_atTop.2 ⟨6, ?_⟩⟩
  intro n hn
  let m := n / 6
  have hm : 0 < m := by dsimp [m]; omega
  obtain ⟨t, ht, hcoll⟩ := exists_few_collisions m hm
  let a : Fin (2 * m) → ℕ := fun i => step m t i
  refine ⟨2 * m, a, (step_strictMono m t hm).comp Fin.val_strictMono, ?_, ?_⟩
  · intro i
    have h := step_bounds m t i hm (mem_range.mp ht) i.isLt
    exact ⟨h.1, h.2.trans (by dsimp [m]; omega)⟩
  · have hsub : (endpoints m).image (intervalValue m t) ⊆ consecutiveSums a := by
      rintro v hv
      obtain ⟨⟨j, i⟩, hp, rfl⟩ := mem_image.mp hv
      obtain ⟨hj, hi⟩ := mem_product.mp hp
      exact value_mem (mem_range.mp hi) (mem_range.mp hj)
    have henergy : m ^ 2 * m ^ 2 ≤ (28 * (consecutiveSums a).card) * m ^ 2 := by
      calc
        _ = (m * m) ^ 2 := by ring
        _ ≤ _ := card_le_image_mul_collisions m t
        _ ≤ (consecutiveSums a).card * (28 * m ^ 2) :=
          Nat.mul_le_mul (card_le_card hsub) hcoll
        _ = _ := by ring
    have hcard : m ^ 2 ≤ 28 * (consecutiveSums a).card :=
      Nat.le_of_mul_le_mul_right henergy (pow_pos hm 2)
    have hn' : n ≤ 12 * m := by dsimp [m]; omega
    have hsquare := Nat.pow_le_pow_left hn' 2
    have hbound : n ^ 2 ≤ 4032 * (consecutiveSums a).card := by nlinarith
    have : (n : ℝ) ^ 2 ≤ 4032 * ((consecutiveSums a).card : ℝ) := by exact_mod_cast hbound
    linarith

end MathlibExt.Combinatorics.IncreasingSequenceConsecutiveSumsErdosProblem356Wanted
