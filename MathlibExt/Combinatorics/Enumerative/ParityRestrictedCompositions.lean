/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import MathlibExt.Combinatorics.Enumerative.ArndtNegativeEven
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Compositions with parity-restricted large parts

Splitting off the first part relates the generating series of compositions into even or small
odd parts to the indicator series of their allowed parts. For compositions into odd or small
even parts, the recurrence follows from the negative-even-shift identity and the generalized
Arndt count recurrence.
-/

namespace MetaMathlibExt

open Finset PowerSeries

private def lengthCount (P : ℕ → Prop) [DecidablePred P] (m n : ℕ) : ℕ :=
  ((Nat.antidiagonalTuple m n).filter fun c ↦ ∀ i, P (c i)).card

private def restrictedCount (P : ℕ → Prop) [DecidablePred P] (n : ℕ) : ℕ :=
  ∑ m ∈ range (n + 1), lengthCount P m n

private lemma lengthCount_succ (P : ℕ → Prop) [DecidablePred P] (m n : ℕ) :
    lengthCount P (m + 1) n =
      ∑ p ∈ (antidiagonal n).filter (fun p ↦ P p.1), lengthCount P m p.2 := by
  classical
  let tails (t : ℕ) := (Nat.antidiagonalTuple m t).filter fun c ↦ ∀ i, P (c i)
  let pieces := ((antidiagonal n).filter fun p ↦ P p.1).sigma fun p ↦ tails p.2
  let join (z : Σ _ : ℕ × ℕ, Fin m → ℕ) : Fin (m + 1) → ℕ := Fin.cons z.1.1 z.2
  let split (c : Fin (m + 1) → ℕ) : Σ _ : ℕ × ℕ, Fin m → ℕ :=
    ⟨(c 0, ∑ i, Fin.tail c i), Fin.tail c⟩
  have mem_pieces (p : ℕ × ℕ) (c : Fin m → ℕ) :
      (⟨p, c⟩ : Σ _ : ℕ × ℕ, Fin m → ℕ) ∈ pieces ↔
        (p.1 + p.2 = n ∧ P p.1) ∧ (∑ i, c i) = p.2 ∧ ∀ i, P (c i) := by
    simp [pieces, tails, Nat.mem_antidiagonalTuple]
  change ((Nat.antidiagonalTuple (m + 1) n).filter fun c ↦ ∀ i, P (c i)).card =
    ∑ p ∈ (antidiagonal n).filter (fun p ↦ P p.1), (tails p.2).card
  rw [← card_sigma]
  change _ = pieces.card
  symm
  apply card_nbij' join split
  · rintro ⟨p, c⟩ hz
    obtain ⟨⟨hp, ha⟩, hc, ht⟩ := (mem_pieces _ _).mp hz
    simp [join, Nat.mem_antidiagonalTuple, Fin.sum_cons, Fin.forall_fin_succ, hp, ha, hc, ht]
  · intro c hc
    obtain ⟨hs, hv⟩ := mem_filter.mp hc
    rw [Nat.mem_antidiagonalTuple, Fin.sum_univ_succ] at hs
    exact (mem_pieces _ _).mpr ⟨⟨hs, hv 0⟩, rfl, fun i ↦ hv i.succ⟩
  · rintro ⟨⟨a, b⟩, c⟩ hz
    have hc := ((mem_pieces _ _).mp hz).2.1
    simp [split, join, hc]
  · intro c _
    exact Fin.cons_self_tail c

private lemma restrictedCount_extend (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ a, P a → 0 < a) {n N : ℕ} (h : n ≤ N) :
    restrictedCount P n = ∑ m ∈ range (N + 1), lengthCount P m n := by
  apply sum_subset (range_mono (by omega))
  intro m _ hm
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro c hc
  obtain ⟨hs, hp⟩ := mem_filter.mp hc
  have hle := sum_le_sum (s := univ) fun i _ ↦ (show 1 ≤ c i from hP (c i) (hp i))
  simp [Nat.mem_antidiagonalTuple.mp hs] at hle
  simp only [mem_range, not_lt] at hm
  omega

-- Partition the nonempty tuples by the first part and the weight of their tail.
private lemma restrictedCount_first (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ a, P a → 0 < a) (n : ℕ) :
    restrictedCount P n = (if n = 0 then 1 else 0) +
      ∑ p ∈ (antidiagonal n).filter (fun p ↦ P p.1), restrictedCount P p.2 := by
  have hnil : lengthCount P 0 n = if n = 0 then 1 else 0 := by
    cases n <;> simp [lengthCount]
  rw [restrictedCount_extend P hP (N := n + 1) (by omega : n ≤ n + 1), sum_range_succ', hnil,
    add_comm]
  simp_rw [lengthCount_succ]
  rw [sum_comm]
  congr 1
  apply sum_congr rfl
  intro p hp
  have h := mem_antidiagonal.mp (mem_filter.mp hp).1
  exact (restrictedCount_extend P hP (N := n) (by omega)).symm

-- The first forbidden part is `s`, and the only other forbidden positive parts
-- are those above `s` with the same parity.
private def allowed (s a : ℕ) : Prop :=
  0 < a ∧ (a % 2 ≠ s % 2 ∨ a < s)

private instance (s : ℕ) : DecidablePred (allowed s) := fun a ↦ by
  unfold allowed
  infer_instance

private noncomputable def countsSeries (s : ℕ) : PowerSeries ℤ :=
  mk fun n ↦ (restrictedCount (allowed s) n : ℤ)

private noncomputable def partsSeries (s : ℕ) : PowerSeries ℤ :=
  mk fun n ↦ if allowed s n then 1 else 0

private lemma decompose (s : ℕ) : countsSeries s = 1 + partsSeries s * countsSeries s := by
  ext n
  have h := congrArg (fun m : ℕ ↦ (m : ℤ))
    (restrictedCount_first (allowed s) (fun _ h ↦ h.1) n)
  simp only [map_add, coeff_one, coeff_mul, countsSeries, partsSeries, coeff_mk]
  rw [Nat.cast_add, Nat.cast_sum] at h
  rw [h, sum_filter]
  congr 1
  · split_ifs <;> rfl
  · apply sum_congr rfl
    intro p _
    split_ifs <;> simp

-- Subtract the indicator shifted by two: the only changes are at 1, 2, and s.
private lemma parts_mul (s : ℕ) (hs : 3 ≤ s) :
    partsSeries s * (1 - X ^ 2) = X + X ^ 2 - X ^ s := by
  ext n
  simp only [mul_sub, mul_one, map_sub, map_add, coeff_mul_X_pow', coeff_X, coeff_X_pow,
    partsSeries, coeff_mk]
  rcases n with _ | _ | _ | n
  · simp [allowed, show 0 ≠ s by omega]
  · simp [allowed, show 1 < s by omega, show 1 ≠ s by omega]
  · simp [allowed, show 2 < s by omega, show 2 ≠ s by omega]
  · have hm : (n + 1 + 1 + 1 - 2) % 2 = (n + 1 + 1 + 1) % 2 := by omega
    simp only [allowed, hm, ite_eq_left (show 2 ≤ n + 1 + 1 + 1 by omega),
      ite_eq_right (show n + 1 + 1 + 1 ≠ 1 by omega),
      ite_eq_right (show n + 1 + 1 + 1 ≠ 2 by omega)]
    split_ifs <;> omega

private lemma restrictedCount_recurrence (s n : ℕ) (hs : 3 ≤ s) (hn : 3 ≤ n) :
    (restrictedCount (allowed s) n : ℤ) = restrictedCount (allowed s) (n - 1) +
      2 * restrictedCount (allowed s) (n - 2) -
      if s ≤ n then (restrictedCount (allowed s) (n - s) : ℤ) else 0 := by
  have hseries : countsSeries s - countsSeries s * X ^ 1 - (countsSeries s * X ^ 2) * 2 +
      countsSeries s * X ^ s = 1 - X ^ 2 := by
    linear_combination (1 - X ^ 2) * decompose s + countsSeries s * parts_mul s hs
  have h := congrArg (coeff (R := ℤ) n) hseries
  simp only [map_add, map_sub, coeff_mul_ofNat, coeff_mul_X_pow', coeff_X_pow, coeff_one,
    countsSeries, coeff_mk, ite_eq_left (show 1 ≤ n by omega), ite_eq_left (show 2 ≤ n by omega),
    ite_eq_right (show n ≠ 0 by omega), ite_eq_right (show n ≠ 2 by omega)] at h
  omega

private lemma restrictedCount_congr {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ a, P a ↔ Q a) (n : ℕ) : restrictedCount P n = restrictedCount Q n := by
  apply sum_congr rfl
  intro m _
  unfold lengthCount
  congr 1
  ext c
  simp only [mem_filter, h]

@[expose] public section

/-- **Compositions into even or small odd parts.** For natural numbers $k$ and $n$,
$c^{2k+1}_e(n)$ is the number of compositions of $n$ (sequences of positive integers of any
length, including the empty one, that sum to $n$) in which every part is even or at most
$2k + 1$. In particular $c^{2k+1}_e(0) = 1$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Definition 5. -/
def evenOrSmallOddCompositionCount (k n : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (n + 1), ((Finset.Nat.antidiagonalTuple m n).filter fun c =>
    ∀ i, 0 < c i ∧ (Even (c i) ∨ c i ≤ 2 * k + 1)).card

private lemma evenOrSmallOdd_eq (k n : ℕ) :
    evenOrSmallOddCompositionCount k n = restrictedCount (allowed (2 * k + 3)) n := by
  change restrictedCount (fun a ↦ 0 < a ∧ (Even a ∨ a ≤ 2 * k + 1)) n = _
  apply restrictedCount_congr
  intro a
  rw [allowed, Nat.even_iff]
  omega

/-- **Recurrences for even-or-small-odd and odd-or-small-even compositions.** For natural
numbers $k$ and $n$, let $c^{2k+1}_e(n)$ be the number of compositions of $n$ in which every part
is even or at most $2k + 1$, and $c^{2k}_o(n)$ the number in which every part is odd or at most
$2k$. If $k \ge 1$ and $n \ge 3$, then
$$c^{2k+1}_e(n) = c^{2k+1}_e(n - 1) + 2c^{2k+1}_e(n - 2) - c^{2k+1}_e(n - 3 - 2k)$$
and
$$c^{2k}_o(n) = c^{2k}_o(n - 1) + 2c^{2k}_o(n - 2) - c^{2k}_o(n - 2 - 2k),$$
where the last term is read as $0$ when its argument is negative.

Both recurrences fail at $n = 2$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Corollary 1 (`integers-2026-A64-cor-1`). -/
public theorem evenOrSmallOdd_oddOrSmallEven_recurrence (k n : ℕ) (hk : 1 ≤ k)
    (hn : 3 ≤ n) :
    ((evenOrSmallOddCompositionCount k n : ℤ) =
        evenOrSmallOddCompositionCount k (n - 1) + 2 * evenOrSmallOddCompositionCount k (n - 2) -
          if 2 * k + 3 ≤ n then (evenOrSmallOddCompositionCount k (n - 3 - 2 * k) : ℤ)
          else 0) ∧
      (oddOrSmallEvenCompositionCount k n : ℤ) =
        oddOrSmallEvenCompositionCount k (n - 1) + 2 * oddOrSmallEvenCompositionCount k (n - 2) -
          if 2 * k + 2 ≤ n then (oddOrSmallEvenCompositionCount k (n - 2 - 2 * k) : ℤ) else 0 := by
  constructor
  · simp only [evenOrSmallOdd_eq]
    rw [show n - 3 - 2 * k = n - (2 * k + 3) by omega]
    exact restrictedCount_recurrence (2 * k + 3) n (by omega) hn
  · have h (m : ℕ) := kArndtTotalCount_neg_even k m hk
    simpa only [Nat.cast_mul, Nat.cast_ofNat, h] using kArndtTotalCount_recurrence.1 (2 * k) n hn

end

end MetaMathlibExt
