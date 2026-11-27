/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.Partition.PeakGeneratingFunction
public import MathlibExt.Combinatorics.Enumerative.SymmetricPeaksCompositions
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.List.OfFn
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.SetPartitionPeaks

/-!
# Non-symmetric peaks in set partitions

We define the non-symmetric peak count and compute the ordinary generating function for its
total over set partitions with a fixed number of blocks.
-/

open Finset PowerSeries

namespace MetaMathlibExt

@[expose] public section

/-- **Non-symmetric peaks of a word.** For a word $w = w_1 w_2 \cdots w_\ell$ of natural numbers,
a non-symmetric peak is a position $i$ with $1 < i < \ell$ such that $w_{i-1} < w_i$,
$w_{i+1} < w_i$ and $w_{i-1} \ne w_{i+1}$. The non-symmetric peak count of $w$ is the number of
such positions; in particular it is $0$ when $\ell < 3$.

A peak with $w_{i-1} = w_{i+1}$ is a symmetric peak instead.

Source: Walaa Asakly and Noor Kezil, *Counting Symmetric and Non-Symmetric Peaks in a Set
Partition*, INTEGERS 26 (2026), Article A8, Section 1. -/
def nonSymmetricPeakCount : List ℕ → ℕ
  | a :: b :: c :: t =>
      (if a < b ∧ c < b ∧ a ≠ c then 1 else 0) + nonSymmetricPeakCount (b :: c :: t)
  | _ => 0

/-- **Peaks of the word $1322141251$.** The word $1322141251$ (the list
$1, 3, 2, 2, 1, 4, 1, 2, 5, 1$) has exactly one symmetric peak, the factor $141$, and exactly two
non-symmetric peaks, the factors $132$ and $251$.

Source: Walaa Asakly and Noor Kezil, *Counting Symmetric and Non-Symmetric Peaks in a Set
Partition*, INTEGERS 26 (2026), Article A8, Section 1. -/
theorem symmetricPeakCount_nonSymmetricPeakCount_example :
    symmetricPeakCount [1, 3, 2, 2, 1, 4, 1, 2, 5, 1] = 1 ∧
      nonSymmetricPeakCount [1, 3, 2, 2, 1, 4, 1, 2, 5, 1] = 2 := by
  decide

end

end MetaMathlibExt

namespace MetaMathlibExt.nonSymmetricPeaks_derivative_generatingFunction

open symmetricPeaks_derivative_generatingFunction (partitionWords sum_partitionWords_snoc
  card_partitionWords)

private lemma words_eq (n k : ℕ) :
    partitionWords n k =
      univ.filter (fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w) := by
  ext w
  simp [partitionWords, IsSurjectiveRestrictedGrowthString]

private def labels {n k : ℕ} (w : Fin n → Fin k) : List ℕ := List.ofFn fun i => (w i).val

private def peaks {n k : ℕ} (w : Fin n → Fin k) : ℕ := nonSymmetricPeakCount (labels w)

private def total (n k : ℕ) : ℕ := ∑ w ∈ partitionWords n k, peaks w

private lemma labels_succ {n k : ℕ} (w : Fin (n + 1) → Fin k) :
    labels w = labels (Fin.init w) ++ [(w (Fin.last n)).val] := by
  unfold labels
  rw [List.ofFn_succ', List.concat_eq_append]
  rfl

private lemma append_triple (l : List ℕ) (a b c : ℕ) :
    nonSymmetricPeakCount (l ++ [a, b, c]) =
      nonSymmetricPeakCount (l ++ [a, b]) + (if a < b ∧ c < b ∧ a ≠ c then 1 else 0) := by
  match l with
  | [] | [_] | [_, _] => simp [nonSymmetricPeakCount, Nat.add_assoc]
  | x :: y :: z :: t =>
    simpa only [List.cons_append, nonSymmetricPeakCount, Nat.add_assoc] using
      congrArg ((if x < y ∧ z < y ∧ x ≠ z then 1 else 0) + ·)
        (append_triple (y :: z :: t) a b c)

private lemma peaks_snoc {n k : ℕ} (w : Fin (n + 2) → Fin k) (c : Fin k) :
    peaks (Fin.snoc w c) = peaks w +
      if w (Fin.last n).castSucc < w (Fin.last (n + 1)) ∧
        c < w (Fin.last (n + 1)) ∧ w (Fin.last n).castSucc ≠ c then 1 else 0 := by
  unfold peaks
  rw [labels_succ (Fin.snoc w c), Fin.init_snoc, Fin.snoc_last,
    labels_succ w, labels_succ (Fin.init w)]
  simpa only [List.append_assoc, List.cons_append, List.nil_append, ne_eq, Fin.val_inj, Fin.init,
    Fin.lt_def] using
    append_triple (labels (Fin.init (Fin.init w))) (w (Fin.last n).castSucc).val
      (w (Fin.last (n + 1))).val c.val

private lemma peaks_new {n k : ℕ} (w : Fin (n + 2) → Fin k) :
    peaks (Fin.snoc (Fin.castSucc ∘ w) (Fin.last k)) = peaks w := by
  rw [peaks_snoc]
  simp [Function.comp_apply, not_lt_of_ge (Fin.le_last _)]
  rfl

private def riseWeight {k : ℕ} (a b : Fin k) : ℕ := if a < b then b.val - 1 else 0

private def finalRise {n k : ℕ} (w : Fin (n + 2) → Fin k) : ℕ :=
  riseWeight (w (Fin.last n).castSucc) (w (Fin.last (n + 1)))

-- A rise a < b can be closed by any letter below b except a.
private lemma count_endings {k : ℕ} (a b : Fin k) :
    ∑ c : Fin k, (if a < b ∧ c < b ∧ a ≠ c then 1 else 0 : ℕ) = riseWeight a b := by
  by_cases h : a < b
  · have hfilter : (univ.filter fun c : Fin k => c < b ∧ a ≠ c) = (Iio b).erase a := by
      ext c
      simp [ne_comm, and_comm]
    simp only [riseWeight, h, true_and, ite_true, sum_boole, hfilter,
      card_erase_of_mem (mem_Iio.mpr h), Fin.card_Iio, Nat.cast_id]
  · simp [riseWeight, h]

private lemma peaks_old {n k : ℕ} (w : Fin (n + 2) → Fin k) :
    ∑ c : Fin k, peaks (Fin.snoc w c) = k * peaks w + finalRise w := by
  simp_rw [peaks_snoc, sum_add_distrib, count_endings]
  simp [finalRise]

private lemma total_step (n k : ℕ) :
    total (n + 3) (k + 1) = total (n + 2) k + (k + 1) * total (n + 2) (k + 1) +
      ∑ w ∈ partitionWords (n + 2) (k + 1), finalRise w := by
  unfold total
  rw [sum_partitionWords_snoc]
  simp_rw [peaks_new, peaks_old, sum_add_distrib, ← mul_sum, Nat.add_assoc]

private lemma sum_fixed_top {k : ℕ} (b : Fin k) :
    ∑ a : Fin k, riseWeight a b = b.val * (b.val - 1) := by
  calc
    _ = ∑ _a ∈ Iio b, (b.val - 1) := by
      rw [← filter_gt_eq_Iio, sum_filter]
      rfl
    _ = _ := by simp

private lemma sum_riseWeight (k : ℕ) :
    ∑ a : Fin k, ∑ b : Fin k, riseWeight a b = 2 * k.choose 3 := by
  rw [sum_comm]
  simp_rw [sum_fixed_top]
  rw [Fin.sum_univ_eq_sum_range (fun b => b * (b - 1))]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih, Nat.choose_succ_succ, Nat.mul_add,
      Nat.choose_two_right, Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self k), add_comm]

-- An introduced maximum gives k - 1 possible closing letters. If both final letters
-- are old, their weighted count is the number of ordered choices of two smaller letters
-- below a common maximum.
private lemma sum_finalRise (n k : ℕ) :
    ∑ w ∈ partitionWords (n + 2) (k + 1), finalRise w =
      (k - 1) * (partitionWords (n + 1) k).card +
        (2 * (k + 1).choose 3) * (partitionWords n (k + 1)).card := by
  rw [sum_partitionWords_snoc (n + 1)]
  simp only [finalRise, Fin.snoc_castSucc, Fin.snoc_last, Function.comp_apply]
  have newWeight (a : Fin k) : riseWeight a.castSucc (Fin.last k) = k - 1 := by
    simp [riseWeight]
  simp only [newWeight, sum_const, smul_eq_mul]
  rw [sum_partitionWords_snoc n]
  have lastWeight (b : Fin (k + 1)) : riseWeight (Fin.last k) b = 0 := by
    simp [riseWeight, not_lt_of_ge (Fin.le_last b)]
  simp only [Fin.snoc_last, lastWeight, sum_const_zero, zero_add, sum_riseWeight,
    sum_const, smul_eq_mul]
  ac_rfl

private lemma total_short (n k : ℕ) (hn : n ≤ 2) : total n k = 0 := by
  apply sum_eq_zero
  intro w _
  match n with
  | 0 | 1 | 2 => simp [peaks, labels, List.ofFn_succ, nonSymmetricPeakCount]
  | n + 3 => omega

private lemma no_peak_of_small_letters (l : List ℕ) (h : ∀ a ∈ l, a < 2) :
    nonSymmetricPeakCount l = 0 := by
  match l with
  | [] | [_] | [_, _] => rfl
  | a :: b :: c :: t =>
    have hb := h b (by simp)
    rw [nonSymmetricPeakCount, ite_eq_right (by omega), zero_add]
    exact no_peak_of_small_letters (b :: c :: t) fun x hx => h x (.tail _ hx)

private lemma total_small (n k : ℕ) (hk : k ≤ 2) : total n k = 0 := by
  apply sum_eq_zero
  intro w _
  apply no_peak_of_small_letters
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  exact (w i).isLt.trans_le hk

private noncomputable def counts (k : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun n => ((partitionWords n k).card : ℤ)

private noncomputable def totals (k : ℕ) : ℤ⟦X⟧ := PowerSeries.mk fun n => (total n k : ℤ)

private lemma counts_mul_denom (k : ℕ) :
    counts (k + 1) * (1 - (↑(k + 1) : ℤ⟦X⟧) * X) = X * counts k := by
  calc
    _ = counts (k + 1) - X * ((↑(k + 1) : ℤ⟦X⟧) * counts (k + 1)) := by ring
    _ = _ := by
      ext n
      cases n with
      | zero => simp [counts, card_partitionWords]
      | succ n =>
        simp only [map_sub, coeff_succ_X_mul, coeff_natCast_mul, counts, coeff_mk,
          card_partitionWords, Nat.stirlingSecond_succ_succ]
        push_cast
        ring

private lemma totals_step (k : ℕ) :
    totals (k + 1) = X * totals k + X * ((↑(k + 1) : ℤ⟦X⟧) * totals (k + 1)) +
      X * (X * ((↑(k - 1) : ℤ⟦X⟧) * counts k)) +
      X * (X * (X * ((↑(2 * (k + 1).choose 3) : ℤ⟦X⟧) * counts (k + 1)))) := by
  ext n
  match n with
  | 0 | 1 | 2 =>
    simp only [map_add, coeff_zero_X_mul, coeff_succ_X_mul, coeff_natCast_mul,
      totals, counts, coeff_mk, card_partitionWords]
    cases k <;> simp [total_short]
  | n + 3 =>
    simp only [map_add, coeff_succ_X_mul, coeff_natCast_mul, totals, counts, coeff_mk]
    rw [total_step n k, sum_finalRise]
    push_cast
    ring

private noncomputable def geom (k : ℕ) : ℤ⟦X⟧ := invOfUnit (1 - (k : ℤ⟦X⟧) * X) 1

private lemma geom_inverse (k : ℕ) : (1 - (k : ℤ⟦X⟧) * X) * geom k = 1 :=
  mul_invOfUnit _ _ (by simp)

private lemma generating_function_small (k : ℕ) (hk : k ≤ 2) :
    totals k = (↑((k - 1).choose 2) : ℤ⟦X⟧) * X * counts k +
      counts k * ∑ m ∈ Icc 3 k, 2 * X ^ 3 * (↑(m.choose 3) : ℤ⟦X⟧) * geom m := by
  have hchoose : (k - 1).choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have hIcc : Icc 3 k = ∅ := Icc_eq_empty_of_lt (by omega)
  simp only [hchoose, Nat.cast_zero, zero_mul, hIcc, sum_empty, mul_zero, add_zero]
  ext n
  simp [totals, total_small n k hk]

private noncomputable def contribution (m : ℕ) : ℤ⟦X⟧ :=
  2 * X ^ 3 * (↑(m.choose 3) : ℤ⟦X⟧) * geom m

private lemma generating_function (k : ℕ) :
    totals k = (↑((k - 1).choose 2) : ℤ⟦X⟧) * X * counts k +
      counts k * ∑ m ∈ Icc 3 k, contribution m := by
  by_cases hk : k < 2
  · exact generating_function_small k (by omega)
  push Not at hk
  induction k, hk using Nat.le_induction with
  | base => exact generating_function_small 2 (by decide)
  | succ k hk ih =>
    rw [sum_Icc_succ_top (by omega : 3 ≤ k + 1)]
    let D : ℤ⟦X⟧ := 1 - (↑(k + 1) : ℤ⟦X⟧) * X
    have hg : D * geom (k + 1) = 1 := geom_inverse (k + 1)
    have hc : X * counts k * geom (k + 1) = counts (k + 1) := by
      rw [← counts_mul_denom k, mul_assoc, hg, mul_one]
    have ht : totals (k + 1) * D = X * totals k + (↑(k - 1) : ℤ⟦X⟧) * X ^ 2 * counts k +
        2 * X ^ 3 * (↑((k + 1).choose 3) : ℤ⟦X⟧) * counts (k + 1) := by
      dsimp only [D]
      have h := totals_step k
      push_cast at h ⊢
      linear_combination h
    have hchoose : k.choose 2 = (k - 1).choose 2 + (k - 1) := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
      change (j + 1).choose 2 = j.choose 2 + j
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      exact add_comm _ _
    let S := ∑ j ∈ Icc 3 k, contribution j
    calc
      totals (k + 1) = totals (k + 1) * D * geom (k + 1) := by rw [mul_assoc, hg, mul_one]
      _ = ((↑(k.choose 2) : ℤ⟦X⟧) * X + S) * (X * counts k * geom (k + 1)) +
          counts (k + 1) * contribution (k + 1) := by
        rw [ht, ih, hchoose]
        simp only [Nat.cast_add, S, contribution]
        ring
      _ = _ := by rw [hc, Nat.add_sub_cancel]; ring

end MetaMathlibExt.nonSymmetricPeaks_derivative_generatingFunction

namespace MetaMathlibExt

open nonSymmetricPeaks_derivative_generatingFunction

/-- **Generating function for the total number of non-symmetric peaks in set partitions.** Fix
$k \in \mathbb{N}$ and, for each $n$, let $P_{n,k}$ be the set of surjective restricted-growth
strings of length $n$ with letters in $\{0, \dots, k-1\}$; these encode the partitions of
$\{1, \dots, n\}$ into exactly $k$ blocks. For $w \in P_{n,k}$ let $\operatorname{nsp}(w)$ be the
number of non-symmetric peaks of $w$. In the ring $\mathbb{Z}[[x]]$ of formal power series let
$F_k(x) = \sum_{n \ge 0} |P_{n,k}| x^n$. Then
$$
\sum_{n \ge 0} \Big(\sum_{w \in P_{n,k}} \operatorname{nsp}(w)\Big) x^n =
\binom{k - 1}{2} x F_k(x) + F_k(x) \sum_{m=3}^{k} 2 \binom{m}{3} \frac{x^3}{1 - m x},
$$
where $k - 1$ is read as $0$ when $k = 0$ and $1/(1 - m x)$ is the inverse of $1 - m x$ in
$\mathbb{Z}[[x]]$.

If $NSP_k(x, q) = \sum_{n \ge 0} \sum_{w \in P_{n,k}} q^{\operatorname{nsp}(w)} x^n$, then
$F_k(x) = NSP_k(x, 1)$ and the left side is the derivative of $NSP_k(x, q)$ in $q$ at $q = 1$.

Source: Walaa Asakly and Noor Kezil, *Counting Symmetric and Non-Symmetric Peaks in a Set
Partition*, INTEGERS 26 (2026), Article A8, Lemma 2 (`integers-2026-A8-lem-2`). -/
public theorem nonSymmetricPeaks_derivative_generatingFunction (k : ℕ) :
    let NSP : ℤ⟦X⟧ := PowerSeries.mk fun n =>
      ((univ.filter fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w).card : ℤ)
    PowerSeries.mk (fun n => ((∑ w ∈ univ.filter
        (fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w),
        nonSymmetricPeakCount (List.ofFn fun i => (w i : ℕ)) : ℕ) : ℤ)) =
      (((k - 1).choose 2 : ℕ) : ℤ⟦X⟧) * X * NSP +
        NSP * ∑ m ∈ Icc 3 k, 2 * X ^ 3 * ((m.choose 3 : ℕ) : ℤ⟦X⟧) *
          invOfUnit (1 - ((m : ℕ) : ℤ⟦X⟧) * X) 1 := by
  simpa only [totals, total, counts, words_eq, peaks, labels, contribution, geom] using
    generating_function k

end MetaMathlibExt
