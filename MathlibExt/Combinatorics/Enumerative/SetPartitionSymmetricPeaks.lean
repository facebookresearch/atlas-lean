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
import MathlibExt.Combinatorics.Enumerative.SetPartitionPeaks
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring

/-!
# Symmetric peaks in set partitions

We compute the ordinary generating function for the total number of symmetric peaks among
set partitions with a fixed number of blocks, by counting the peaks created by a final letter.
-/

open Finset PowerSeries

namespace MetaMathlibExt.symmetricPeaks_derivative_generatingFunction

private lemma words_eq (n k : ℕ) :
    partitionWords n k =
      univ.filter (fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w) := by
  ext w
  simp [partitionWords, IsSurjectiveRestrictedGrowthString]

private def labels {n k : ℕ} (w : Fin n → Fin k) : List ℕ := List.ofFn fun i => (w i).val

private def peaks {n k : ℕ} (w : Fin n → Fin k) : ℕ := symmetricPeakCount (labels w)

private def total (n k : ℕ) : ℕ := ∑ w ∈ partitionWords n k, peaks w

private lemma labels_succ {n k : ℕ} (w : Fin (n + 1) → Fin k) :
    labels w = labels (Fin.init w) ++ [(w (Fin.last n)).val] := by
  unfold labels
  rw [List.ofFn_succ', List.concat_eq_append]
  rfl

private lemma append_triple (l : List ℕ) (a b c : ℕ) :
    symmetricPeakCount (l ++ [a, b, c]) =
      symmetricPeakCount (l ++ [a, b]) + (if a = c ∧ a < b then 1 else 0) := by
  match l with
  | [] | [_] | [_, _] => simp [symmetricPeakCount, Nat.add_assoc]
  | x :: y :: z :: t =>
    simpa only [List.cons_append, symmetricPeakCount, Nat.add_assoc] using
      congrArg ((if x = z ∧ x < y then 1 else 0) + ·) (append_triple (y :: z :: t) a b c)

private lemma peaks_snoc {n k : ℕ} (w : Fin (n + 2) → Fin k) (c : Fin k) :
    peaks (Fin.snoc w c) = peaks w +
      if w (Fin.last n).castSucc = c ∧ w (Fin.last n).castSucc < w (Fin.last (n + 1))
      then 1 else 0 := by
  unfold peaks
  rw [labels_succ (Fin.snoc w c), Fin.init_snoc, Fin.snoc_last,
    labels_succ w, labels_succ (Fin.init w)]
  simpa only [List.append_assoc, List.cons_append, List.nil_append, Fin.val_inj, Fin.init,
    Fin.lt_def] using
    append_triple (labels (Fin.init (Fin.init w))) (w (Fin.last n).castSucc).val
      (w (Fin.last (n + 1))).val c.val

private def rise {n k : ℕ} (w : Fin (n + 2) → Fin k) : ℕ :=
  if w (Fin.last n).castSucc < w (Fin.last (n + 1)) then 1 else 0

private lemma peaks_new {n k : ℕ} (w : Fin (n + 2) → Fin k) :
    peaks (Fin.snoc (Fin.castSucc ∘ w) (Fin.last k)) = peaks w := by
  rw [peaks_snoc]
  simp [Function.comp_apply, Fin.castSucc_ne_last]
  rfl

private lemma peaks_old {n k : ℕ} (w : Fin (n + 2) → Fin k) :
    ∑ c : Fin k, peaks (Fin.snoc w c) = k * peaks w + rise w := by
  simp_rw [peaks_snoc, sum_add_distrib]
  by_cases h : w (Fin.last n).castSucc < w (Fin.last (n + 1)) <;>
    simp [h, rise]

-- An appended old letter closes a symmetric peak exactly when it repeats the
-- penultimate letter of a word ending in a rise.
private lemma total_step (n k : ℕ) :
    total (n + 3) (k + 1) = total (n + 2) k + (k + 1) * total (n + 2) (k + 1) +
      ∑ w ∈ partitionWords (n + 2) (k + 1), rise w := by
  unfold total
  rw [sum_partitionWords_snoc]
  simp_rw [peaks_new, peaks_old, sum_add_distrib, ← mul_sum, Nat.add_assoc]

private lemma increasing_pairs (k : ℕ) :
    ∑ a : Fin k, ∑ b : Fin k, (if a < b then 1 else 0 : ℕ) = k.choose 2 := by
  rw [sum_comm]
  calc
    _ = ∑ b : Fin k, b.val := by
      apply sum_congr rfl
      intro b _
      simp only [sum_boole, filter_gt_eq_Iio, Fin.card_Iio, Nat.cast_id]
    _ = _ := by rw [Fin.sum_univ_eq_sum_range (fun i => i), sum_range_id, Nat.choose_two_right]

-- The new maximum always completes a rise after a nonempty prefix. For two old
-- letters at the end, each increasing pair is possible over every valid prefix.
private lemma sum_rise (n k : ℕ) :
    ∑ w ∈ partitionWords (n + 2) (k + 1), rise w =
      (partitionWords (n + 1) k).card + (partitionWords n (k + 1)).card * (k + 1).choose 2 := by
  rw [sum_partitionWords_snoc (n + 1)]
  simp only [rise, Fin.snoc_castSucc, Fin.snoc_last, Function.comp_apply,
    Fin.castSucc_lt_last, ite_true, sum_const, smul_eq_mul, mul_one]
  rw [sum_partitionWords_snoc n]
  simp only [Fin.snoc_last, not_lt_of_ge (Fin.le_last _), ite_false, sum_const_zero,
    zero_add, increasing_pairs, sum_const, smul_eq_mul]

private lemma total_short (n k : ℕ) (hn : n ≤ 2) : total n k = 0 := by
  apply sum_eq_zero
  intro w _
  match n with
  | 0 | 1 | 2 => simp [peaks, labels, List.ofFn_succ, symmetricPeakCount]
  | n + 3 => omega

private lemma no_peak_of_small_letters (l : List ℕ) (h : ∀ a ∈ l, a ≤ 0) :
    symmetricPeakCount l = 0 := by
  match l with
  | [] | [_] | [_, _] => rfl
  | a :: b :: c :: t =>
    have hb := h b (by simp)
    rw [symmetricPeakCount, ite_eq_right (by omega), zero_add]
    exact no_peak_of_small_letters (b :: c :: t) fun x hx => h x (.tail _ hx)

private lemma total_small (n k : ℕ) (hk : k ≤ 1) : total n k = 0 := by
  apply sum_eq_zero
  intro w _
  apply no_peak_of_small_letters
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  have hi := (w i).isLt
  omega

private noncomputable def counts (k : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun n => ((partitionWords n k).card : ℤ)

private noncomputable def totals (k : ℕ) : ℤ⟦X⟧ := PowerSeries.mk fun n => (total n k : ℤ)

private lemma counts_step (k : ℕ) :
    counts (k + 1) = X * counts k + X * ((↑(k + 1) : ℤ⟦X⟧) * counts (k + 1)) := by
  ext n
  cases n with
  | zero => simp [counts, card_partitionWords]
  | succ n =>
    simp only [map_add, coeff_succ_X_mul, coeff_natCast_mul, counts, coeff_mk, card_partitionWords]
    rw [Nat.stirlingSecond_succ_succ]
    push_cast
    ring

private lemma totals_step (k : ℕ) :
    totals (k + 2) = X * totals (k + 1) + X * ((↑(k + 2) : ℤ⟦X⟧) * totals (k + 2)) +
      X * (X * counts (k + 1)) +
      X * (X * (X * ((↑((k + 2).choose 2) : ℤ⟦X⟧) * counts (k + 2)))) := by
  ext n
  match n with
  | 0 | 1 | 2 =>
    simp only [map_add, coeff_zero_X_mul, coeff_succ_X_mul, coeff_natCast_mul,
      totals, counts, coeff_mk, card_partitionWords]
    simp [total_short]
  | n + 3 =>
    simp only [map_add, coeff_succ_X_mul, coeff_natCast_mul, totals, counts, coeff_mk]
    rw [total_step n (k + 1), sum_rise]
    push_cast
    ring

private noncomputable def geom (k : ℕ) : ℤ⟦X⟧ := invOfUnit (1 - (k : ℤ⟦X⟧) * X) 1

private lemma geom_inverse (k : ℕ) : (1 - (k : ℤ⟦X⟧) * X) * geom k = 1 :=
  mul_invOfUnit _ _ (by simp)

private lemma counts_mul_denom (k : ℕ) :
    counts (k + 1) * (1 - (↑(k + 1) : ℤ⟦X⟧) * X) = X * counts k := by
  linear_combination counts_step k

private lemma totals_small (k : ℕ) (hk : k ≤ 1) : totals k = 0 := by
  ext n
  simp [totals, total_small n k hk]

private noncomputable def contribution (m : ℕ) : ℤ⟦X⟧ :=
  X ^ 3 * (↑(m.choose 2) : ℤ⟦X⟧) * geom m

private lemma generating_function (k : ℕ) :
    totals k = (↑(k - 1) : ℤ⟦X⟧) * X * counts k +
      counts k * ∑ m ∈ Icc 1 k, contribution m := by
  induction k with
  | zero => simp [totals_small]
  | succ k ih =>
    cases k with
    | zero => simp [totals_small, contribution]
    | succ k =>
      rw [sum_Icc_succ_top (by omega : 1 ≤ (k + 1) + 1)]
      let m := k + 2
      let D : ℤ⟦X⟧ := 1 - (m : ℤ⟦X⟧) * X
      have hg : D * geom m = 1 := geom_inverse m
      have hc : X * counts (k + 1) * geom m = counts m := by
        rw [← counts_mul_denom (k + 1), mul_assoc, hg, mul_one]
      have ht : totals m * D = X * totals (k + 1) + X ^ 2 * counts (k + 1) +
          X ^ 3 * (↑(m.choose 2) : ℤ⟦X⟧) * counts m := by
        dsimp only [m, D]
        linear_combination totals_step k
      let S := ∑ j ∈ Icc 1 (k + 1), contribution j
      change totals m = (↑(k + 1) : ℤ⟦X⟧) * X * counts m + counts m * (S + contribution m)
      calc
        totals m = totals m * D * geom m := by rw [mul_assoc, hg, mul_one]
        _ = ((↑(k + 1) : ℤ⟦X⟧) * X + S) * (X * counts (k + 1) * geom m) +
            counts m * contribution m := by
          rw [ht, ih]
          simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, S, contribution]
          ring
        _ = _ := by rw [hc]; ring

end MetaMathlibExt.symmetricPeaks_derivative_generatingFunction

namespace MetaMathlibExt

open symmetricPeaks_derivative_generatingFunction

/-- **Generating function for the total number of symmetric peaks in set partitions.** Fix
$k \in \mathbb{N}$ and, for each $n$, let $P_{n,k}$ be the set of surjective restricted-growth
strings of length $n$ with letters in $\{0, \dots, k-1\}$; these encode the partitions of
$\{1, \dots, n\}$ into exactly $k$ blocks. For $w \in P_{n,k}$ let $\operatorname{sp}(w)$ be the
number of symmetric peaks of $w$. In the ring $\mathbb{Z}[[x]]$ of formal power series let
$F_k(x) = \sum_{n \ge 0} |P_{n,k}| x^n$. Then
$$
\sum_{n \ge 0} \Big(\sum_{w \in P_{n,k}} \operatorname{sp}(w)\Big) x^n =
\max(k - 1, 0)\, x F_k(x) + F_k(x) \sum_{m=1}^{k} \binom{m}{2} \frac{x^3}{1 - m x},
$$
where $1/(1 - m x)$ is the inverse of $1 - m x$ in $\mathbb{Z}[[x]]$.

If $SP_k(x, q) = \sum_{n \ge 0} \sum_{w \in P_{n,k}} q^{\operatorname{sp}(w)} x^n$, then
$F_k(x) = SP_k(x, 1)$ and the left side is the derivative of $SP_k(x, q)$ in $q$ at $q = 1$.

Source: Walaa Asakly and Noor Kezil, *Counting Symmetric and Non-Symmetric Peaks in a Set
Partition*, INTEGERS 26 (2026), Article A8, Lemma 1 (`integers-2026-A8-lem-1`). -/
public theorem symmetricPeaks_derivative_generatingFunction (k : ℕ) :
    let SP : ℤ⟦X⟧ := PowerSeries.mk fun n =>
      ((univ.filter fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w).card : ℤ)
    PowerSeries.mk (fun n => ((∑ w ∈ univ.filter
        (fun w : Fin n → Fin k => IsSurjectiveRestrictedGrowthString w),
        symmetricPeakCount (List.ofFn fun i => (w i : ℕ)) : ℕ) : ℤ)) =
      ((k - 1 : ℕ) : ℤ⟦X⟧) * X * SP +
        SP * ∑ m ∈ Icc 1 k, X ^ 3 * ((m.choose 2 : ℕ) : ℤ⟦X⟧) *
          invOfUnit (1 - ((m : ℕ) : ℤ⟦X⟧) * X) 1 := by
  simpa only [totals, total, counts, words_eq, peaks, labels, contribution, geom] using
    generating_function k

end MetaMathlibExt
