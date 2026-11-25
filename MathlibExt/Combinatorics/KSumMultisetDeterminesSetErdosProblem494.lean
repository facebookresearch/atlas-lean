/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Powerset

import Mathlib.Data.Nat.Choose.Consecutive
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.Algebra.Polynomial.RootPowerSums
import MathlibExt.NumberTheory.RothAuxiliary

/-!
# Reconstruction from multisets of subset sums

For each fixed subset size at least three, the multiset of subset sums and the cardinality
determine every sufficiently large finite set of complex numbers.

The power-sum argument uses the Moser coefficients. The first differing power sum forces one of
these integer coefficients to vanish. Reduction modulo a prime divisor of the cardinality then
bounds all its prime factors. In the alternating sum defining the coefficient, ratios between
successive terms decrease geometrically in the moment order. Cancellation forces two adjacent
terms to agree up to an exponentially small relative error. Extracting powers from the bounded
prime factors and applying Roth's theorem forces the corresponding approximation to be exact.
The third term rules out the last possible exact equality.

See D. Fomin, *Is the Multiset of n Integers Uniquely Determined by the Multiset of Its
s-sums?*, [arXiv:1709.06046](https://arxiv.org/abs/1709.06046).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.KSumMultisetDeterminesSetErdosProblem494Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #494, https://www.erdosproblems.com/494 (status
PROVED). UnsolvedMath record UM-30006901 (`EP-494`), dataset ulamai/UnsolvedMath v1.8.0.

Taken with `|A|` large in terms of `k`, as erdosproblems.com/494 does: the literal question fails
for `|A| = k` (rotations about the centroid) and `|A| = 2k` (Tao). `A_k` is a multiset, and `|A| =
|B|` is a hypothesis. Compared with the formal-conjectures statement `ErdosProblems/494.lean` (it
records the k = 2 and k = 3, 4 cases of Selfridge and Straus; no code imported).
-/

/-- **Multiset of $k$-sums.** For a finite set $A \subseteq \mathbb{C}$ and a natural number $k$,
$A_k$ is the multiset of the sums $\sum_{z \in S} z$ over the $k$-element subsets $S$ of $A$, that
is, of the sums of $k$ distinct elements of $A$, each subset counted once. -/
noncomputable def kSumMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map fun s => ∑ z ∈ s, z

/-- **Erdős Problem 494 for large sets.** For a finite set $A \subseteq \mathbb{C}$ and a natural
number $k$, let $A_k$ be the multiset of the sums of the $k$-element subsets of $A$. This is the
statement that for every natural number $k \ge 3$ there is a natural number $n_0$ such that any
two finite sets $A, B \subseteq \mathbb{C}$ with $|A| = |B| \ge n_0$ and $A_k = B_k$ are equal.

This is the question of Selfridge and Straus with $|A|$ large in terms of $k$. -/
def kSumMultisetDeterminesLargeSet : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∃ n₀ : ℕ, ∀ A B : Finset ℂ, A.card = B.card → n₀ ≤ A.card →
    kSumMultiset A k = kSumMultiset B k → A = B

open Finset Filter Topology

/- The order-m power sum of the k-subset sums. -/
private def moment (A : Finset ℂ) (k m : ℕ) : ℂ :=
  ∑ s ∈ A.powersetCard k, (∑ z ∈ s, z) ^ m

private lemma sum_insert_subsets {A : Finset ℂ} {z : ℂ} (hz : z ∉ A) (k : ℕ)
    (f : Finset ℂ → ℂ) :
    ∑ s ∈ (insert z A).powersetCard (k + 1), f s =
    ∑ s ∈ A.powersetCard (k + 1), f s + ∑ s ∈ A.powersetCard k, f (insert z s) := by
  classical
  rw [powersetCard_succ_insert hz, sum_union, sum_image]
  · intro a ha b hb hab
    have hza : z ∉ a := fun h => hz ((mem_powersetCard.mp ha).1 h)
    have hzb : z ∉ b := fun h => hz ((mem_powersetCard.mp hb).1 h)
    simpa [hza, hzb] using congrArg (fun s : Finset ℂ => s.erase z) hab
  · rw [disjoint_left]
    intro s hs h
    obtain ⟨t, _, rfl⟩ := mem_image.mp h
    exact hz ((mem_powersetCard.mp hs).1 (mem_insert_self _ _))

/- Remove subsets containing the marked element by repeated subtraction. -/
private lemma erase_sum {A : Finset ℂ} {z : ℂ} (hz : z ∈ A) (k : ℕ)
    (f : ℂ → ℂ) :
    ∑ s ∈ (A.erase z).powersetCard k, f (∑ x ∈ s, x) =
    ∑ j ∈ range (k + 1), (-1 : ℂ) ^ j *
      ∑ s ∈ A.powersetCard (k - j), f (j * z + ∑ x ∈ s, x) := by
  classical
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    have h := sum_insert_subsets (notMem_erase z A) k (fun s => f (∑ x ∈ s, x))
    rw [insert_erase hz] at h
    have shift : ∑ s ∈ (A.erase z).powersetCard k, f (∑ x ∈ insert z s, x) =
        ∑ s ∈ (A.erase z).powersetCard k, f (z + ∑ x ∈ s, x) := by
      apply sum_congr rfl
      intro s hs
      rw [sum_insert (fun h => (notMem_erase z A) ((mem_powersetCard.mp hs).1 h))]
    rw [shift, ih (fun y => f (z + y))] at h
    rw [sum_range_succ']
    simp only [Nat.succ_sub_succ_eq_sub, Nat.cast_add, Nat.cast_one, pow_succ, mul_neg,
      mul_one, neg_mul, sum_neg_distrib, pow_zero, one_mul, Nat.sub_zero,
      Nat.cast_zero, zero_mul, zero_add]
    have inc (j : ℕ) (t : ℂ) : ((j : ℂ) + 1) * z + t = z + (j * z + t) := by ring
    simp only [inc]
    linear_combination -h

/- Mark one summand in each subset and expand the remaining power by the binomial theorem. -/
private lemma moment_succ (A : Finset ℂ) (k m : ℕ) :
    moment A (k + 1) (m + 1) = ∑ j ∈ range (k + 1), (-1 : ℂ) ^ j *
      ∑ l ∈ range (m + 1), ((j : ℂ) + 1) ^ l * m.choose l *
        (∑ z ∈ A, z ^ (l + 1)) * moment A (k - j) (m - l) := by
  classical
  have marked : moment A (k + 1) (m + 1) = ∑ z ∈ A, z *
      ∑ s ∈ (A.erase z).powersetCard k, (z + ∑ x ∈ s, x) ^ m := by
    unfold moment
    simp_rw [pow_succ, mul_comm _ (∑ x ∈ _, x), sum_mul]
    rw [sum_comm' (s' := fun z => (A.powersetCard (k + 1)).filter (z ∈ ·)) (t' := A)
      (by intro s z; grind)]
    apply sum_congr rfl
    intro z hz
    rw [← mul_sum]
    congr 1
    have hfilter : ((A.powersetCard (k + 1)).filter (z ∈ ·)) =
        ((A.erase z).powersetCard k).image (insert z) := by
      ext s
      simp only [mem_filter, mem_powersetCard, mem_image]
      constructor
      · rintro ⟨⟨hs, hc⟩, hz'⟩
        exact ⟨s.erase z, ⟨erase_subset_erase _ hs, by simp [card_erase_of_mem hz', hc]⟩,
          insert_erase hz'⟩
      · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
        have hz' : z ∉ t := fun h => notMem_erase _ _ (ht h)
        exact ⟨⟨insert_subset hz (ht.trans (erase_subset _ _)), by simp [hz', hc]⟩,
          mem_insert_self _ _⟩
    rw [hfilter, sum_image]
    · apply sum_congr rfl
      intro s hs
      rw [sum_insert (fun h => notMem_erase _ _ ((mem_powersetCard.mp hs).1 h))]
    · intro a ha b hb hab
      have hza : z ∉ a := fun h => notMem_erase _ _ ((mem_powersetCard.mp ha).1 h)
      have hzb : z ∉ b := fun h => notMem_erase _ _ ((mem_powersetCard.mp hb).1 h)
      simpa [hza, hzb] using congrArg (fun s : Finset ℂ => s.erase z) hab
  rw [marked]
  simp_rw [sum_congr rfl (fun z hz => congrArg (z * ·) (erase_sum hz k
    (fun y => (z + y) ^ m)))]
  simp_rw [mul_sum, ← mul_assoc]
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  have shift (z t : ℂ) : z + (j * z + t) = ((j : ℂ) + 1) * z + t := by ring
  conv_lhs => simp only [shift, add_pow (((j : ℂ) + 1) * _) _, mul_pow, mul_sum]
  conv_lhs =>
    enter [2, z]
    rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro l hl
  unfold moment
  simp_rw [mul_sum, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro s hs
  apply sum_congr rfl
  intro z hz
  ring

private lemma moment_eq {A B : Finset ℂ} (hc : A.card = B.card) (d : ℕ)
    (h : ∀ l ≤ d, ∑ z ∈ A, z ^ l = ∑ z ∈ B, z ^ l) (k : ℕ) :
    moment A k d = moment B k d := by
  induction d using Nat.strong_induction_on generalizing k with
  | ind d ih =>
    cases d with
    | zero => simp [moment, hc]
    | succ m =>
      cases k with
      | zero => simp [moment]
      | succ k =>
        rw [moment_succ, moment_succ]
        apply sum_congr rfl
        intro j _
        congr 1
        apply sum_congr rfl
        intro l hl
        have hl' := mem_range.mp hl
        rw [h (l + 1) (by omega), ih (m - l) (by omega) (fun t ht => h _ (by omega))]

private def moser (n k m : ℕ) : ℂ :=
  ∑ j ∈ range k, (-1 : ℂ) ^ j * ((j : ℂ) + 1) ^ m * n.choose (k - 1 - j)

/- If all lower power sums agree, only the term of highest degree survives in the difference. -/
private lemma difference {A B : Finset ℂ} (hc : A.card = B.card) (k m : ℕ)
    (h : ∀ l ≤ m, ∑ z ∈ A, z ^ l = ∑ z ∈ B, z ^ l) :
    moment A (k + 1) (m + 1) - moment B (k + 1) (m + 1) =
      moser A.card (k + 1) m * ((∑ z ∈ A, z ^ (m + 1)) - ∑ z ∈ B, z ^ (m + 1)) := by
  rw [moment_succ, moment_succ, ← sum_sub_distrib]
  unfold moser
  rw [sum_mul]
  apply sum_congr rfl
  intro j _
  rw [← mul_sub, ← sum_sub_distrib, sum_eq_single m]
  · simp [moment, hc]
    ring
  · intro l hl hne
    have hl' := mem_range.mp hl
    rw [h (l + 1) (by omega), moment_eq hc (m - l) (fun t ht => h t (by omega)), sub_self]
  · simp

/- Nonvanishing at every moment order lets us recover the power sums successively. -/
private lemma recover {A B : Finset ℂ} (hc : A.card = B.card) (k : ℕ)
    (h : kSumMultiset A (k + 1) = kSumMultiset B (k + 1))
    (hn : ∀ m, moser A.card (k + 1) m ≠ 0) : A = B := by
  have hall (m : ℕ) : ∑ z ∈ A, z ^ m = ∑ z ∈ B, z ^ m := by
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      cases m with
      | zero => simp [hc]
      | succ m =>
        have he := congrArg (fun M : Multiset ℂ => (M.map (· ^ (m + 1))).sum) h
        simp only [kSumMultiset, Multiset.map_map] at he
        have hm : moment A (k + 1) (m + 1) = moment B (k + 1) (m + 1) := he
        have hd := difference hc k m (fun l hl => ih l (by omega))
        rw [hm, sub_self, eq_comm, mul_eq_zero, or_iff_right (hn m), sub_eq_zero] at hd
        exact hd
  exact Finset.eq_of_veq (Multiset.eq_of_card_eq_of_forall_sum_pow_eq _ _ hc
    (fun m _ => hall m))

/- Modulo a prime divisor of n larger than the subset size, only the last summand survives. -/
private lemma smooth_of_zero (n k m : ℕ) (hk : k ≤ n) (h : moser n (k + 1) m = 0)
    {p : ℕ} (hp : p.Prime) (hd : p ∣ n) : p ≤ k + 1 := by
  by_contra! hpk
  have hZ : ∑ j ∈ range (k + 1), (-1 : ℤ) ^ j * ((j : ℤ) + 1) ^ m * n.choose (k - j) = 0 := by
    unfold moser at h
    exact_mod_cast h
  let _ : Fact p.Prime := ⟨hp⟩
  have hz := congrArg (Int.castRingHom (ZMod p)) hZ
  simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_add, map_natCast, map_zero] at hz
  rw [sum_range_succ] at hz
  have hsum : ∑ j ∈ range k, (-1 : ZMod p) ^ j * ((j : ZMod p) + 1) ^ m * n.choose (k - j) = 0 := by
    apply sum_eq_zero
    intro j hj
    have hlt := mem_range.mp hj
    have hdvd : p ∣ n.choose (k - j) :=
      (hp.dvd_choose_iff (by omega) (by omega)).mpr ⟨0, by omega, by simpa⟩
    simp [(ZMod.natCast_eq_zero_iff _ _).mpr hdvd]
  simp only [hsum, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one, zero_add] at hz
  have hne : ((k + 1 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by omega) hpk
  push_cast at hne
  exact (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (pow_ne_zero _ hne)) hz

/- At a zero of the alternating sum, the largest term has a comparable neighbor.
The decreasing ratios allow us to choose that neighbor adjacent to the maximum. -/
private lemma peak_pair (k : ℕ) (hk : 0 < k) (T R : ℕ → ℝ) (δ : ℝ)
    (hδ : δ ≤ 1) (ht : ∀ i ≤ k, 0 < T i) (hr : ∀ i < k, 0 < R i)
    (step : ∀ i < k, T (i + 1) = R i * T i)
    (sep : ∀ a b, a < b → b < k → R b ≤ δ * R a)
    (zero : ∑ i ∈ range (k + 1), (-1 : ℝ) ^ i * T i = 0) :
    ∃ j < k, 1 ≤ (k + 1 : ℝ) * R j ∧ R j ≤ (k + 1 : ℝ) ∧
      (∀ t ≤ k, T t ≤ (k + 1 : ℝ) * T j) := by
  let S := range (k + 1)
  have hS : S.Nonempty := ⟨0, mem_range.mpr (by omega)⟩
  obtain ⟨a, ha, ham⟩ := exists_max_image S T hS
  have hak := Nat.le_of_lt_succ (mem_range.mp ha)
  have hex : (S.erase a).Nonempty := by
    by_cases h : a = 0
    · exact ⟨1, mem_erase.mpr ⟨by omega, mem_range.mpr (by omega)⟩⟩
    · exact ⟨0, mem_erase.mpr ⟨Ne.symm h, mem_range.mpr (by omega)⟩⟩
  obtain ⟨b, hb, hbm⟩ := exists_max_image _ T hex
  obtain ⟨hne, hb'⟩ := mem_erase.mp hb
  have hbk := Nat.le_of_lt_succ (mem_range.mp hb')
  have za : ∑ i ∈ S.erase a, (-1 : ℝ) ^ i * T i = -((-1 : ℝ) ^ a * T a) := by
    have H := sum_erase_add S (fun i => (-1 : ℝ) ^ i * T i) ha
    rw [show ∑ i ∈ S, (-1 : ℝ) ^ i * T i = 0 from zero] at H
    linarith
  have hab : T a ≤ (k + 1 : ℝ) * T b := calc
    T a = |∑ i ∈ S.erase a, (-1 : ℝ) ^ i * T i| := by simp [za, abs_mul, abs_of_pos (ht a hak)]
    _ ≤ ∑ i ∈ S.erase a, |(-1 : ℝ) ^ i * T i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ S.erase a, T b := by
      apply sum_le_sum
      intro i hi
      simpa [abs_mul, abs_of_pos (ht i (by have := mem_range.mp (mem_of_mem_erase hi); omega))]
        using hbm i hi
    _ ≤ _ := by
      simp only [sum_const, nsmul_eq_mul, card_erase_of_mem ha, S, card_range, Nat.add_sub_cancel]
      nlinarith [ht b hbk]
  have mono {i j : ℕ} (hij : i ≤ j) (hj : j < k) : R j ≤ R i := by
    obtain h | rfl := lt_or_eq_of_le hij
    · exact (sep i j h hj).trans (by nlinarith [hr i (by omega)])
    · rfl
  have maxT {t : ℕ} (htk : t ≤ k) : T t ≤ T a := ham _ (mem_range.mpr (by omega))
  rcases lt_or_gt_of_ne hne with hba | hab'
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
    have hj : j < k := by omega
    have hj1 : 1 ≤ R j := by
      have h := maxT (t := j) (by omega)
      rw [step j hj] at h
      exact (le_mul_iff_one_le_left (ht j (by omega))).mp h
    have hrb : R b ≤ (k + 1 : ℝ) := by
      have h := (maxT (t := b + 1) (by omega)).trans hab
      rwa [step b (by omega), mul_le_mul_iff_left₀ (ht b hbk)] at h
    have hrj := (mono (by omega : b ≤ j) hj).trans hrb
    refine ⟨j, hj, by nlinarith [hr j hj, show (0 : ℝ) ≤ k by positivity], hrj, ?_⟩
    intro t htk
    exact (maxT htk).trans (by rw [step j hj]; exact mul_le_mul_of_nonneg_right hrj (ht j hj.le).le)
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
    have ha' : a < k := by omega
    have hra : R a ≤ 1 := by
      have h := maxT (t := a + 1) (by omega)
      rw [step a ha'] at h
      exact (mul_le_iff_le_one_left (ht a hak)).mp h
    have hT := maxT (t := j) (by omega)
    have hrja := mono (by omega : a ≤ j) (by omega : j < k)
    have hone : 1 ≤ (k + 1 : ℝ) * R a := by
      rw [step j (by omega)] at hab
      have h : T a ≤ ((k + 1 : ℝ) * R a) * T a := by
        apply hab.trans
        rw [mul_assoc]
        gcongr
        · exact (ht j (by omega)).le
        · exact (hr a ha').le
      exact (le_mul_iff_one_le_left (ht a hak)).mp h
    exact ⟨a, ha', hone, by linarith [show (0 : ℝ) ≤ k by positivity],
      fun t htk => (maxT htk).trans (by nlinarith [mul_nonneg (Nat.cast_nonneg k) (ht a hak).le])⟩

private lemma partial_sum_bound (k : ℕ) (T : ℕ → ℝ) (D : Finset ℕ)
    (hD : D ⊆ range (k + 1)) {b : ℝ} (hb : 0 ≤ b)
    (hz : ∑ i ∈ range (k + 1), (-1 : ℝ) ^ i * T i = 0)
    (htail : ∀ i ≤ k, i ∉ D → |T i| ≤ b) :
    |∑ i ∈ D, (-1 : ℝ) ^ i * T i| ≤ (k + 1 : ℝ) * b := by
  let S := range (k + 1) \ D
  have h := sum_sdiff hD (f := fun i => (-1 : ℝ) ^ i * T i)
  rw [hz] at h
  have he : ∑ i ∈ D, (-1 : ℝ) ^ i * T i = -(∑ i ∈ S, (-1 : ℝ) ^ i * T i) := by
    dsimp [S]
    linarith
  rw [he, abs_neg]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum (g := fun _ => b) (fun i hi => ?_)).trans ?_)
  · obtain ⟨hi, hn⟩ := mem_sdiff.mp hi
    simpa [abs_mul] using htail i (by have := mem_range.mp hi; omega) hn
  · rw [sum_const, nsmul_eq_mul]
    have H : S.card ≤ k + 1 := (card_le_card sdiff_subset).trans_eq (card_range _)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast H) hb

/- Outside the two comparable terms, separation of adjacent ratios bounds every term
by a multiple of δ times the peak. The two terms must therefore almost cancel. -/
private lemma ratio_close (k : ℕ) (T R : ℕ → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (ht : ∀ i ≤ k, 0 < T i) (step : ∀ i < k, T (i + 1) = R i * T i)
    (sep : ∀ a b, a < b → b < k → R b ≤ δ * R a)
    (zero : ∑ i ∈ range (k + 1), (-1 : ℝ) ^ i * T i = 0)
    {j : ℕ} (hj : j < k) (hlo : 1 ≤ (k + 1 : ℝ) * R j) (hhi : R j ≤ (k + 1 : ℝ))
    (hmax : ∀ t ≤ k, T t ≤ (k + 1 : ℝ) * T j) :
    |1 - R j| ≤ (k + 1 : ℝ) ^ 3 * δ := by
  let K : ℝ := k + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have tj := ht j hj.le
  have bound := partial_sum_bound k T {j, j + 1} (by
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    exact mem_range.mpr (by omega))
    (b := δ * K ^ 2 * T j) (by positivity) zero (by
      intro i hi hne
      rw [abs_of_pos (ht i hi)]
      simp only [mem_insert, mem_singleton, not_or] at hne
      rcases lt_or_gt_of_ne hne.1 with hij | hij
      · have he := sep i j hij hj
        have hlo' : 1 ≤ K * (δ * R i) := hlo.trans (mul_le_mul_of_nonneg_left he hK.le)
        have hh := mul_le_mul_of_nonneg_right hlo' (ht i hi).le
        calc
          T i ≤ K * δ * T (i + 1) := by rw [step i (by omega)]; linarith only [hh]
          _ ≤ K * δ * (K * T j) := mul_le_mul_of_nonneg_left (hmax _ (by omega)) (by positivity)
          _ = _ := by ring
      · obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
        have he := sep j s (by omega) (by omega)
        rw [step s (by omega)]
        calc
          R s * T s ≤ δ * K * (K * T j) := mul_le_mul
            (he.trans (mul_le_mul_of_nonneg_left hhi hδ)) (hmax _ (by omega))
            (ht _ (by omega)).le (by positivity)
          _ = _ := by ring)
  have hS : ∑ i ∈ ({j, j + 1} : Finset ℕ), (-1 : ℝ) ^ i * T i =
      (-1 : ℝ) ^ j * ((1 - R j) * T j) := by
    rw [sum_insert (by simp), sum_singleton, step j hj, pow_succ]
    ring
  rw [hS, abs_mul, abs_mul] at bound
  simp only [abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos tj] at bound
  apply (mul_le_mul_iff_left₀ tj).mp
  dsimp [K] at bound
  linarith only [bound]

/- Exponential factor in the ratio of successive unsigned Moser summands. -/
private noncomputable def base (i : ℕ) : ℝ := ((i : ℝ) + 2) / (i + 1)

private def term (k n m i : ℕ) : ℝ := ((i : ℝ) + 1) ^ m * n.choose (k - i)

private noncomputable def ratio (k n m i : ℕ) : ℝ :=
  (base i) ^ m * (((k : ℝ) - i) / ((n : ℝ) - k + i + 1))

private lemma base_gt (i : ℕ) : 1 < base i := by
  unfold base
  rw [one_lt_div (by positivity)]
  linarith

/- Choose one rate below one for all the finitely many separations between ratios. -/
private lemma choose_rate (k : ℕ) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∀ a < k, (base a)⁻¹ ≤ θ ∧
      ∀ b, a < b → b < k → base b / base a ≤ θ := by
  have H : ∀ᶠ θ : ℝ in 𝓝[<] 1, ∀ a ∈ range k, (base a)⁻¹ ≤ θ ∧
      ∀ b ∈ range k, a < b → base b / base a ≤ θ := by
    rw [eventually_all_finset]
    intro a _
    apply Filter.Eventually.and
    · exact (eventually_ge_nhds (inv_lt_one_of_one_lt₀ (base_gt a))).filter_mono nhdsWithin_le_nhds
    · rw [eventually_all_finset]
      intro b _
      by_cases h : a < b
      · have hab : base b < base a := by
          unfold base
          rw [div_lt_div_iff₀ (by positivity) (by positivity)]
          nlinarith only [show (a : ℝ) < b by exact_mod_cast h]
        have h' := (div_lt_one ((lt_trans zero_lt_one (base_gt a)))).mpr hab
        exact ((eventually_ge_nhds h').filter_mono nhdsWithin_le_nhds).mono fun _ ht _ => ht
      · simp [h]
  obtain ⟨θ, h, htp, ht⟩ := (H.and ((eventually_gt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
    |>.and (self_mem_nhdsWithin (s := Set.Iio (1 : ℝ))))).exists
  exact ⟨θ, htp, ht, fun a ha => ⟨(h a (mem_range.mpr ha)).1,
    fun b hba hb => (h _ (mem_range.mpr ha)).2 b (mem_range.mpr hb) hba⟩⟩

private lemma term_pos (k n m i : ℕ) (hn : k ≤ n) : 0 < term k n m i := by
  dsimp [term]
  have h := Nat.choose_pos (show k - i ≤ n by omega)
  positivity

private lemma ratio_pos {k n m i : ℕ} (hn : k ≤ n) (hi : i < k) :
    0 < ratio k n m i := by
  dsimp [ratio]
  have h1 : (0 : ℝ) < (k : ℝ) - i := sub_pos.mpr (by exact_mod_cast hi)
  have h2 : (0 : ℝ) ≤ (n : ℝ) - k := sub_nonneg.mpr (by exact_mod_cast hn)
  have h3 := base_gt i
  positivity

private lemma term_step {k n m i : ℕ} (hn : k ≤ n) (hi : i < k) :
    term k n m (i + 1) = ratio k n m i * term k n m i := by
  have h := Nat.choose_succ_right_eq n (k - (i + 1))
  rw [show k - (i + 1) + 1 = k - i by omega] at h
  have e : (n.choose (k - i) : ℝ) * ((k : ℝ) - i) =
      n.choose (k - (i + 1)) * ((n : ℝ) - k + i + 1) := by
    have he := congrArg (Nat.cast (R := ℝ)) h
    push_cast [Nat.cast_sub (by omega : i + 1 ≤ k), Nat.cast_sub hi.le,
      Nat.cast_sub (by omega : k - (i + 1) ≤ n)] at he
    linarith only [he]
  unfold term ratio base
  push_cast
  have h2 : (0 : ℝ) ≤ (n : ℝ) - k := sub_nonneg.mpr (by exact_mod_cast hn)
  have hden : (n : ℝ) - k + i + 1 ≠ 0 := by positivity
  rw [show (i : ℝ) + 1 + 1 = i + 2 by ring, div_pow]
  field_simp
  linear_combination -e

private lemma ratio_sep {k n m a b : ℕ} {θ : ℝ} (hn : k ≤ n) (ha : a < b) (hb : b < k)
    (hθ : base b / base a ≤ θ) :
    ratio k n m b ≤ θ ^ m * ratio k n m a := by
  have hab : (a : ℝ) ≤ b := by exact_mod_cast ha.le
  have hbk : (b : ℝ) ≤ k := by exact_mod_cast hb.le
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast hn
  have ha0 := (zero_lt_one.trans (base_gt a))
  have hb0 := (zero_lt_one.trans (base_gt b))
  have hh : base b ≤ θ * base a := (div_le_iff₀ ha0).mp hθ
  have hinc : ((k : ℝ) - b) / ((n : ℝ) - k + b + 1) ≤ ((k : ℝ) - a) / ((n : ℝ) - k + a + 1) := by
    apply div_le_div₀ <;> linarith [show (0 : ℝ) ≤ a by positivity]
  unfold ratio
  rw [← mul_assoc, ← mul_pow]
  have hpos := hb0.trans_le hh
  gcongr

/- Reduce every prime exponent modulo D. The remaining factor d is uniformly bounded. -/
private lemma powers_of_smooth (K D n : ℕ) (hD : D ≠ 0) (hn : n ≠ 0)
    (hs : ∀ p ∈ n.primeFactors, p ≤ K) :
    ∃ d ≤ (∏ p ∈ range (K + 1), (p + 1) ^ D), ∃ u, n = d * u ^ D := by
  let f := n.factorization
  refine ⟨∏ p ∈ n.primeFactors, p ^ (f p % D), ?_,
    ∏ p ∈ n.primeFactors, p ^ (f p / D), ?_⟩
  · calc
      _ ≤ ∏ p ∈ n.primeFactors, (p + 1) ^ D := by
        apply Finset.prod_le_prod
        intro p hp
        have hp0 := (Nat.prime_of_mem_primeFactors hp).one_le
        exact (Nat.pow_le_pow_left (by omega : p ≤ p + 1) _).trans
          (Nat.pow_le_pow_right (by omega) (Nat.mod_lt _ (Nat.pos_of_ne_zero hD)).le)
      _ ≤ _ := prod_le_prod_of_subset_of_one_le (fun p hp => mem_range.mpr (by
        have := hs _ hp
        omega)) (fun p _ _ => Nat.one_le_pow _ _ (by omega))
  · rw [← prod_pow, ← prod_mul_distrib]
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
    apply prod_congr rfl
    intro p _
    rw [← pow_mul, ← pow_add, Nat.mul_comm (f p / D), Nat.mod_add_div]

private lemma root_distance {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (D : ℕ) :
    |x - y| * y ^ D ≤ |x ^ (D + 1) - y ^ (D + 1)| := by
  have ht : y ^ D ≤ ∑ i ∈ range (D + 1), x ^ i * y ^ (D - i) := by
    simpa using single_le_sum (f := fun i => x ^ i * y ^ (D - i)) (fun _ _ => by positivity)
      (mem_range.mpr (Nat.zero_lt_succ D))
  have hid := geom_sum₂_mul x y (D + 1)
  simp only [Nat.add_sub_cancel] at hid
  rw [← hid, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ∑ i ∈ range (D + 1), x ^ i * y ^ (D - i))]
  exact (mul_le_mul_of_nonneg_left ht (abs_nonneg _)).trans_eq (mul_comm ..)

private lemma finite_roth_approximants (c : ℝ) (hc : IsAlgebraic ℚ c) :
    {q : ℚ | |c - (q : ℝ)| < 1 / (q.den : ℝ) ^ 3}.Finite := by
  have h := MathlibExt.NumberTheory.RothAuxiliary.finite_of_divisible_approximations
    c hc 1 zero_lt_one le_rfl (∅ : Finset (Fin 0)) (fun i => i.elim0)
    (fun i => i.elim0) (fun i => i.elim0) (by simp) (by simp) (by norm_num)
  norm_num at h ⊢
  exact h

/- With the residual factors i and j fixed, u/v approximates the positive algebraic
root of c*j/i. Its denominator is at most v. Choosing the extracted power large enough
puts u/v in a finite set of Roth approximants, and exponential convergence forces equality. -/
private lemma fixed_residues (B i j c D : ℕ) (hi : 0 < i) (hj : 0 < j)
    (hc : 0 < c) (r : ℝ) (hr : 0 < r) (hr' : r < 1)
    (hdec : r ^ (D + 1) * (B : ℝ) ^ 3 < 1) :
    ∀ᶠ m : ℕ in atTop, ∀ u v : ℕ, 0 < v → j * v ^ (D + 1) ≤ B ^ m →
      |(i : ℝ) * (u / v : ℝ) ^ (D + 1) / j - c| ≤ r ^ m →
        (i : ℝ) * (u / v : ℝ) ^ (D + 1) / j = c := by
  let y : ℝ := ((c : ℝ) * j / i) ^ ((D + 1 : ℕ) : ℝ)⁻¹
  have hy : 0 < y := Real.rpow_pos_of_pos (by positivity) _
  have hyp : y ^ (D + 1) = (c : ℝ) * j / i :=
    Real.rpow_inv_natCast_pow (by positivity) (by omega)
  have hya : IsAlgebraic ℚ y := by
    apply IsAlgebraic.of_pow (n := D + 1) (by omega)
    rw [hyp]
    simpa [map_div₀, map_mul] using isAlgebraic_algebraMap (R := ℚ) (A := ℝ) ((c : ℚ) * j / i)
  let C := (j : ℝ) / (i * y ^ D)
  have hC : 0 < C := by dsimp [C]; positivity
  have dec : ∀ᶠ m : ℕ in atTop, C ^ (D + 1) * (r ^ (D + 1) * (B : ℝ) ^ 3) ^ m < 1 := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hdec).const_mul (C ^ (D + 1))
    exact h.eventually_lt_const (by simp)
  have fin := finite_roth_approximants y hya
  have excl : ∀ᶠ m : ℕ in atTop, ∀ q ∈ {q : ℚ | |y - (q : ℝ)| < 1 / (q.den : ℝ) ^ 3},
      (q : ℝ) ≠ y → C * r ^ m < |(q : ℝ) - y| := by
    rw [fin.eventually_all]
    intro q _
    by_cases h : (q : ℝ) = y
    · simp [h]
    · exact ((tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr').const_mul C
        |>.eventually_lt_const (by simpa using abs_pos.mpr (sub_ne_zero.mpr h))).mono
        (fun _ hm _ => hm)
  filter_upwards [dec, excl] with m hm he u v hv hb herr
  let q : ℚ := (u : ℚ) / v
  have hq : (q : ℝ) = (u : ℝ) / v := by simp [q]
  have den : q.den ≤ v := by
    have hd := Rat.den_dvd u v
    simp only [Rat.divInt_eq_div, Int.cast_natCast] at hd
    exact Nat.le_of_dvd hv (by exact_mod_cast hd)
  have err : |(q : ℝ) - y| ≤ C * r ^ m := by
    rw [show C * r ^ m = ((j : ℝ) / (i : ℝ) * r ^ m) / y ^ D by dsimp [C]; ring]
    apply (le_div_iff₀ (pow_pos hy D)).mpr
    exact le_trans (root_distance (by rw [hq]; positivity) hy D) (by
      rw [hyp, hq]
      have eq : (u / v : ℝ) ^ (D + 1) - ↑c * ↑j / ↑i =
          (((i : ℝ) * (u / v : ℝ) ^ (D + 1) / j) - c) * ((j : ℝ) / i) := by field_simp
      rw [eq, abs_mul, abs_of_pos (by positivity : 0 < (j : ℝ) / i)]
      simpa [mul_comm] using mul_le_mul_of_nonneg_right herr (by positivity : 0 ≤ (j : ℝ) / i))
  have hvb : (v : ℝ) ^ (D + 1) ≤ (B : ℝ) ^ m := by
    exact_mod_cast (Nat.le_trans (Nat.le_mul_of_pos_left _ hj) hb)
  have hpow : (|(q : ℝ) - y| * (q.den : ℝ) ^ 3) ^ (D + 1) < 1 := calc
    _ ≤ (C * r ^ m * (v : ℝ) ^ 3) ^ (D + 1) := by gcongr
    _ = C ^ (D + 1) * (r ^ (D + 1)) ^ m * ((v : ℝ) ^ (D + 1)) ^ 3 := by ring
    _ ≤ C ^ (D + 1) * (r ^ (D + 1)) ^ m * ((B : ℝ) ^ m) ^ 3 := by gcongr
    _ = C ^ (D + 1) * (r ^ (D + 1) * (B : ℝ) ^ 3) ^ m := by ring
    _ < 1 := hm
  have qmem : q ∈ {q : ℚ | |y - (q : ℝ)| < 1 / (q.den : ℝ) ^ 3} := by
    change |y - (q : ℝ)| < 1 / (q.den : ℝ) ^ 3
    apply (lt_div_iff₀ (by positivity)).mpr
    rw [abs_sub_comm]
    exact lt_of_not_ge (fun h => hpow.not_ge (one_le_pow₀ h))
  have hqy : (q : ℝ) = y := by_contra fun h => (he q qmem h).not_ge err
  rw [← hq, hqy, hyp]
  field_simp

/- An exponentially accurate approximation by smooth integers with exponentially bounded
denominator must eventually be exact. -/
private lemma smooth_approx (B K c : ℕ) (hc : 0 < c) (r : ℝ) (hr : 0 < r) (hr' : r < 1) :
    ∀ᶠ m : ℕ in atTop, ∀ a b : ℕ, 0 < a → 0 < b → b ≤ B ^ m →
      (∀ p ∈ a.primeFactors, p ≤ K) → (∀ p ∈ b.primeFactors, p ≤ K) →
      |(a / b : ℝ) - c| ≤ r ^ m → (a / b : ℝ) = c := by
  have h0 := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr').mul_const ((B : ℝ) ^ 3)
    |>.eventually_lt_const (by simp : 0 * (B : ℝ) ^ 3 < 1))
  obtain ⟨D, hD⟩ := eventually_atTop.mp h0
  let L := ∏ p ∈ range (K + 1), (p + 1) ^ (D + 1)
  have hres : ∀ᶠ m : ℕ in atTop, ∀ i ∈ Icc 1 L, ∀ j ∈ Icc 1 L,
      ∀ u v : ℕ, 0 < v → j * v ^ (D + 1) ≤ B ^ m →
      |(i : ℝ) * (u / v : ℝ) ^ (D + 1) / j - c| ≤ r ^ m →
        (i : ℝ) * (u / v : ℝ) ^ (D + 1) / j = c := by
    rw [eventually_all_finset]
    intro i hi
    rw [eventually_all_finset]
    intro j hj
    exact fixed_residues B i j c D (mem_Icc.mp hi).1 (mem_Icc.mp hj).1 hc r hr hr'
      (hD (D + 1) (by omega))
  filter_upwards [hres] with m hm a b ha hb hbm hsa hsb he
  obtain ⟨i, hi, u, rfl⟩ := powers_of_smooth K (D + 1) a (by omega) ha.ne' hsa
  obtain ⟨j, hj, v, rfl⟩ := powers_of_smooth K (D + 1) b (by omega) hb.ne' hsb
  have h : ((i * u ^ (D + 1) : ℕ) : ℝ) / ((j * v ^ (D + 1) : ℕ) : ℝ) =
      (i : ℝ) * (u / v : ℝ) ^ (D + 1) / j := by
    push_cast
    rw [div_pow]
    ring
  rw [h] at he ⊢
  exact hm i (mem_Icc.mpr ⟨Nat.pos_of_mul_pos_right ha, hi⟩) j
    (mem_Icc.mpr ⟨Nat.pos_of_mul_pos_right hb, hj⟩) u v
    (Nat.pos_of_ne_zero (by rintro rfl; simp at hb)) hbm he

/- Convert almost-equality of adjacent terms into an approximation by a smooth ratio. -/
private lemma edge_error (k n m j : ℕ) (hn : k ≤ n) (hj : j < k)
    {θ : ℝ} (hθ : (base j)⁻¹ ≤ θ)
    (hlo : 1 ≤ (k + 1 : ℝ) * ratio k n m j)
    (hclose : |1 - ratio k n m j| ≤ (k + 1 : ℝ) ^ 3 * θ ^ m) :
    |(n : ℝ) * (base j)⁻¹ ^ m - (k - j : ℝ)| ≤
      ((k + 1 : ℝ) ^ 5 + (k + 1 : ℝ)) * θ ^ m := by
  let R := ratio k n m j
  let K := (k + 1 : ℝ)
  have hjk : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast hn
  have hn' : 0 < (n : ℝ) - k + j + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
  have hbj : 0 < base j := zero_lt_one.trans (base_gt j)
  have hθp := (inv_pos.mpr hbj).trans_le hθ
  have hR : 0 < R := ratio_pos hn hj
  have hK : 0 < K := by dsimp [K]; positivity
  have hid : (n : ℝ) * (base j)⁻¹ ^ m - (k - j : ℝ) =
      ((k : ℝ) - j) * (R⁻¹ - 1) + ((k : ℝ) - j - 1) * (base j)⁻¹ ^ m := by
    dsimp [R, ratio]
    have : (k : ℝ) - j ≠ 0 := by linarith
    rw [inv_pow]
    field_simp
    ring
  have hrec : |R⁻¹ - 1| ≤ K ^ 4 * θ ^ m := calc
    _ = |1 - R| * R⁻¹ := by
      rw [show R⁻¹ - 1 = (1 - R) * R⁻¹ by field_simp, abs_mul, abs_of_pos (inv_pos.mpr hR)]
    _ ≤ (K ^ 3 * θ ^ m) * K := mul_le_mul hclose
      ((inv_le_iff_one_le_mul₀ hR).mpr (by simpa [mul_comm] using hlo))
      (inv_nonneg.mpr hR.le) (by positivity)
    _ = _ := by ring
  rw [hid]
  calc
    _ ≤ |((k : ℝ) - j) * (R⁻¹ - 1)| + |((k : ℝ) - j - 1) * (base j)⁻¹ ^ m| := abs_add_le ..
    _ ≤ K * (K ^ 4 * θ ^ m) + K * θ ^ m := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ (k : ℝ) - j),
        abs_of_nonneg (by linarith : 0 ≤ (k : ℝ) - j - 1), abs_of_nonneg (by positivity :
          0 ≤ (base j)⁻¹ ^ m)]
      have h1 : (k : ℝ) - j ≤ K := by dsimp [K]; linarith [Nat.cast_nonneg (α := ℝ) j]
      have h2 : (k : ℝ) - j - 1 ≤ K := by linarith
      gcongr
    _ = _ := by dsimp [K]; ring

private lemma real_zero {n k m : ℕ} (h : moser n (k + 1) m = 0) :
    ∑ i ∈ range (k + 1), (-1 : ℝ) ^ i * term k n m i = 0 := by
  have hZ : ∑ j ∈ range (k + 1), (-1 : ℤ) ^ j * ((j : ℤ) + 1) ^ m * n.choose (k - j) = 0 := by
    unfold moser at h
    exact_mod_cast h
  unfold term
  simp_rw [← mul_assoc]
  exact_mod_cast hZ

/- Consecutive bases are coprime. In an exact equality the denominator power divides k-j. -/
private lemma exact_center {k n m j : ℕ} (hj : j < k) (hm : k < 2 ^ m)
    (h : (n : ℝ) * (base j)⁻¹ ^ m = (k - j : ℝ)) : j = 0 ∧ n = k * 2 ^ m := by
  have e : n * (j + 1) ^ m = (k - j) * (j + 2) ^ m := by
    apply Nat.cast_injective (R := ℝ)
    push_cast [Nat.cast_sub hj.le]
    unfold base at h
    rw [inv_div, div_pow, ← mul_div_assoc] at h
    exact (div_eq_iff (by positivity)).mp h
  have cp : (j + 1).Coprime (j + 2) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  have hdiv : (j + 1) ^ m ∣ (k - j) :=
    ((cp.pow_left m).pow_right m).dvd_of_dvd_mul_right (e ▸ dvd_mul_left _ _)
  have hj0 : j = 0 := by
    by_contra hne
    have hle := Nat.le_of_dvd (by omega : 0 < k - j) hdiv
    have hbig := Nat.pow_le_pow_left (by omega : 2 ≤ j + 1) m
    omega
  subst j
  simpa using e

/- At the first center, the difference between the first two terms is too small to
cancel the third term. Every later term is smaller still. -/
private lemma exclude_first_center {k n m : ℕ} (hk : 2 ≤ k) (hn : k ≤ n)
    {δ : ℝ} (hδ : 0 ≤ δ) (hs : δ * (k + 1 : ℝ) ^ 2 < 1 / 3)
    (hm : 3 ≤ (3 / 2 : ℝ) ^ m) (he : n = k * 2 ^ m)
    (hR : ratio k n m 0 ≤ (k + 1 : ℝ))
    (sep : ∀ a b, a < b → b < k → ratio k n m b ≤ δ * ratio k n m a) :
    ∑ i ∈ range (k + 1), (-1 : ℝ) ^ i * term k n m i ≠ 0 := by
  let T := term k n m
  let R := ratio k n m
  let K : ℝ := k + 1
  have hK : 1 ≤ K := by dsimp [K]; simp
  have small : δ * K < 1 := by
    nlinarith [mul_nonneg hδ (show 0 ≤ K * (K - 1) by positivity), show δ * K ^ 2 < 1 / 3 from hs]
  have hr {s : ℕ} (h : 0 < s) (hs : s < k) : R s ≤ δ * K :=
    (sep 0 s h hs).trans (mul_le_mul_of_nonneg_left hR hδ)
  have tpos (i : ℕ) := term_pos k n m i hn
  have tail {s : ℕ} (h : 2 ≤ s) (hs : s ≤ k) : T s ≤ T 2 := by
    induction s, h using Nat.le_induction with
    | base => rfl
    | succ s h ih =>
      change term k n m (s + 1) ≤ _
      rw [term_step hn (by omega)]
      have hRle := (hr (s := s) (by omega) (by omega)).trans small.le
      exact ((mul_le_iff_le_one_left (tpos s)).mpr hRle).trans (ih (by omega))
  intro zero
  have hb := partial_sum_bound k T (range 3) (range_mono (by omega))
    (b := δ * K * T 2) (by have := tpos 2; change 0 ≤ δ * K * term k n m 2; positivity) zero (by
      intro i hi him
      rw [abs_of_pos (tpos i)]
      have hi3 : 3 ≤ i := by simpa using him
      obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      exact (term_step hn (by omega : s < k)).le.trans
        (mul_le_mul (hr (by omega) (by omega)) (tail (by omega) (by omega))
          (tpos s).le (by positivity)))
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast hn
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have he' : (n : ℝ) = k * (2 : ℝ) ^ m := by exact_mod_cast he
  have d0 : T 1 * ((n : ℝ) - k + 1) = n * T 0 := by
    have h := term_step (m := m) hn (show 0 < k by omega)
    change T 1 = ratio k n m 0 * T 0 at h
    norm_num [ratio, base] at h
    have hh : (n : ℝ) - k + 1 ≠ 0 := by linarith
    calc
      _ = (2 : ℝ) ^ m * k * T 0 := by rw [h]; field_simp
      _ = _ := by rw [he']; ring
  have d1 : T 2 * ((n : ℝ) - k + 2) = (3 / 2 : ℝ) ^ m * ((k : ℝ) - 1) * T 1 := by
    have h := term_step (m := m) hn (show 1 < k by omega)
    change T 2 = ratio k n m 1 * T 1 at h
    norm_num [ratio, base] at h
    rw [h, show (n : ℝ) - k + 2 = n - k + 1 + 1 by ring]
    have hh : (n : ℝ) - k + 1 + 1 ≠ 0 := by linarith
    field_simp
  have hdiff : 3 * (T 1 - T 0) ≤ T 2 := by
    apply (le_of_mul_le_mul_right (a := (n : ℝ)) _ hn0)
    calc
      3 * (T 1 - T 0) * n = 3 * ((k : ℝ) - 1) * T 1 := by linarith only [d0]
      _ ≤ (3 / 2 : ℝ) ^ m * ((k : ℝ) - 1) * T 1 := by gcongr <;> linarith [tpos 1]
      _ = T 2 * ((n : ℝ) - k + 2) := d1.symm
      _ ≤ T 2 * n := by gcongr <;> linarith [tpos 2]
  have ht2 : 0 < T 2 := tpos 2
  have hlt : K * (δ * K * T 2) < T 2 / 3 := by
    have h := mul_lt_mul_of_pos_right hs ht2
    dsimp [K]
    linarith only [h]
  norm_num [sum_range_succ] at hb
  have h := (le_abs_self _).trans hb
  linarith

private lemma round_center (k : ℕ) {r : ℝ} (hr : 0 < r) (hr' : r < 1) :
    ∀ᶠ m : ℕ in atTop, ∀ j ∈ range k, ∀ n : ℕ, 0 < n →
      (∀ p ∈ n.primeFactors, p ≤ k + 1) →
      |(n : ℝ) * (base j)⁻¹ ^ m - (k - j : ℝ)| ≤ r ^ m →
      (n : ℝ) * (base j)⁻¹ ^ m = (k - j : ℝ) := by
  rw [eventually_all_finset]
  intro j hj
  have hjk := mem_range.mp hj
  filter_upwards [smooth_approx (k + 1) (k + 1) (k - j) (by omega) r hr hr'] with m H n hn hs h
  have identity : ((n * (j + 1) ^ m : ℕ) : ℝ) / (((j + 2) ^ m : ℕ) : ℝ) =
      (n : ℝ) * (base j)⁻¹ ^ m := by
    push_cast
    rw [base, inv_div, div_pow]
    ring
  have hnum : ∀ p ∈ (n * (j + 1) ^ m).primeFactors, p ≤ k + 1 := by
    intro p hp
    have pp := Nat.prime_of_mem_primeFactors hp
    rcases pp.dvd_mul.mp (Nat.dvd_of_mem_primeFactors hp) with hd | hd
    · exact hs _ (Nat.mem_primeFactors.mpr ⟨pp, hd, hn.ne'⟩)
    · have := Nat.le_of_dvd (by omega : 0 < j + 1) (pp.dvd_of_dvd_pow hd)
      omega
  have hden : ∀ p ∈ ((j + 2) ^ m).primeFactors, p ≤ k + 1 := by
    intro p hp
    have := Nat.le_of_dvd (by omega : 0 < j + 2)
      ((Nat.prime_of_mem_primeFactors hp).dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hp))
    omega
  have res := H (n * (j + 1) ^ m) ((j + 2) ^ m) (by positivity) (by positivity)
    (Nat.pow_le_pow_left (by omega) _) hnum hden
  rw [identity, Nat.cast_sub hjk.le] at res
  exact res h

/- Large moment orders force an impossible exact equality. The finitely many smaller
orders give a uniform cardinality bound directly from the ratio at the peak. -/
private lemma moser_nonzero (k : ℕ) (hk : 2 ≤ k) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m, moser n (k + 1) m ≠ 0 := by
  obtain ⟨θ, hθ, hθ', hbase⟩ := choose_rate k
  obtain ⟨r, htr, hr⟩ := exists_between hθ'
  have hr0 := hθ.trans htr
  let K : ℝ := k + 1
  let C := K ^ 5 + K
  have hK : 0 < K := by dsimp [K]; positivity
  have bound : ∀ᶠ m : ℕ in atTop, C * θ ^ m ≤ r ^ m := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (div_pos hθ hr0).le
      ((div_lt_one hr0).mpr htr)).const_mul C |>.eventually_lt_const (by simp : C * 0 < 1)
    filter_upwards [h] with m hm
    rw [div_pow, ← mul_div_assoc, div_lt_one (pow_pos hr0 _)] at hm
    exact hm.le
  have hsmall := (tendsto_pow_atTop_nhds_zero_of_lt_one hθ.le hθ').mul_const (K ^ 2)
    |>.eventually_lt_const (by norm_num : 0 * K ^ 2 < (1 / 3 : ℝ))
  have hthird : ∀ᶠ m : ℕ in atTop, (3 : ℝ) ≤ (3 / 2 : ℝ) ^ m :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3 / 2)).eventually_ge_atTop 3
  have hbig : ∀ᶠ m : ℕ in atTop, k < 2 ^ m :=
    (tendsto_pow_atTop_atTop_of_one_lt (by decide : (1 : ℕ) < 2)).eventually_gt_atTop k
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    ((round_center k hr0 hr).and (bound.and (hsmall.and (hthird.and hbig))))
  refine ⟨k + (k + 1) * 2 ^ M * k + 1, ?_⟩
  intro n hn m hz
  have hkn : k ≤ n := by omega
  have hz' := real_zero hz
  have sep (a b : ℕ) (hab : a < b) (hb : b < k) := ratio_sep (m := m) hkn hab hb
    ((hbase a (by omega)).2 b hab hb)
  obtain ⟨j, hj, hlo, hhi, hmax⟩ := peak_pair k (by omega) (term k n m) (ratio k n m) (θ ^ m)
    (pow_le_one₀ hθ.le hθ'.le) (fun i _ => term_pos k n m i hkn)
    (fun _ hi => ratio_pos hkn hi) (fun _ hi => term_step hkn hi) sep hz'
  by_cases hm : M ≤ m
  · obtain ⟨hround, hbd, hsm, hth, hbig'⟩ := hM m hm
    have hclose := ratio_close k _ _ (pow_nonneg hθ.le m) (fun i _ => term_pos k n m i hkn)
      (fun _ hi => term_step hkn hi) sep hz' hj hlo hhi hmax
    have hedge := (edge_error k n m j hkn hj (hbase j hj).1 hlo hclose).trans hbd
    have eq := hround j (mem_range.mpr hj) n (by omega) (fun p hp => smooth_of_zero n k m hkn hz
      (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)) hedge
    obtain ⟨rfl, he⟩ := exact_center hj hbig' eq
    exact exclude_first_center hk hkn (pow_nonneg hθ.le m) hsm hth he hhi sep hz'
  · have hn' : (k : ℝ) + (k + 1 : ℝ) * 2 ^ M * k + 1 ≤ n := by exact_mod_cast hn
    have hj' : (j : ℝ) < k := by exact_mod_cast hj
    have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
    have hj0 : 0 ≤ (j : ℝ) := by positivity
    have hden : 0 < (n : ℝ) - k + j + 1 := by linarith
    unfold ratio at hlo
    rw [← mul_assoc, ← mul_div_assoc, one_le_div hden] at hlo
    have hb : base j ≤ 2 := by
      unfold base
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hpow : (base j) ^ m ≤ (2 : ℝ) ^ M :=
      (pow_le_pow_left₀ (zero_lt_one.trans (base_gt j)).le hb m).trans
        (pow_le_pow_right₀ (by norm_num) (by omega))
    have hle : ((k : ℝ) + 1) * (base j) ^ m * ((k : ℝ) - j) ≤
        ((k : ℝ) + 1) * 2 ^ M * k := by
      gcongr
      linarith
    linarith

/--
**Large sets of complex numbers are determined by their $k$-sums.** For a finite set
$A \subseteq \mathbb{C}$ and a natural number $k$, let $A_k$ be the multiset of the sums
$\sum_{z \in S} z$ over the $k$-element subsets $S$ of $A$. For every natural number $k \ge 3$
there is a natural number $n_0$ such that any two finite sets $A, B \subseteq \mathbb{C}$ with
$|A| = |B| \ge n_0$ and $A_k = B_k$ are equal.

Gordon, Fraenkel and Straus proved (Section 4) that for $s > 2$ two $n$-element multisets in a
torsion-free abelian group with the same multiset of $s$-sums are equal for all but finitely many
$n$; $\mathbb{C}$ is torsion-free and sets are multisets.

Source: T. F. Bloom, Erdős Problems,
Problem #494, https://www.erdosproblems.com/494 (status PROVED); resolution: B. Gordon, A. S.
Fraenkel and E. G. Straus, On the determination of sets by the sets of sums of a certain order,
Pacific J. Math. 12 (1962), 187-196, Section 4: for s > 2, F_s(n) = 1 for all but finitely many n,
for finite multisets in any torsion-free abelian group, https://doi.org/10.2140/pjm.1962.12.187.
-/
theorem kSumMultisetDeterminesLargeSet_holds : kSumMultisetDeterminesLargeSet := by
  intro t ht
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  obtain ⟨N,hN⟩ := moser_nonzero k (by omega)
  exact ⟨N, fun A B hc hcard he => recover hc k he (hN A.card hcard)⟩

end MathlibExt.Combinatorics.KSumMultisetDeterminesSetErdosProblem494Wanted
