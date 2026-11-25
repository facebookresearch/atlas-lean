/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Recurrences for generalized Arndt counts

Removing the first pair of parts gives a convolution for the generalized Arndt counts.
The generating series of admissible pairs gives the two recurrences in
`kArndtTotalCount_recurrence`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Number of $k$-Arndt compositions.** For an integer $k$ and $n, m \ge 0$, $a_k(n, m)$ is the
number of $k$-Arndt compositions of $n$ with $m$ parts: sequences $(c_0, \ldots, c_{m-1})$ of
positive integers with $c_0 + \cdots + c_{m-1} = n$ such that $c_{2i} > c_{2i+1} + k$ for every
$i \ge 0$ with $2i + 1 < m$. For $k = 0$ these are the Arndt compositions.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 4 (definition of `k`-Arndt compositions,
after Hopkins and Tangboonduangjit; Theorem 11 treats `k ≥ 0` and `k < 0`). -/
def kArndtCompositionCount (k : ℤ) (n m : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple m n).filter fun c =>
    (∀ i, 0 < c i) ∧
      ∀ i j : Fin m, (i : ℕ) % 2 = 0 → (j : ℕ) = i + 1 → (c j : ℤ) + k < c i).card

/-- **Sample values of the $k$-Arndt composition counts.** Writing $a_k(n, m)$ for the number of
$k$-Arndt compositions of $n$ with $m$ parts, $a_3(7, 2) = 1$, $a_3(7, 3) = 1$ and
$a_{-3}(4, 2) = 3$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Section 4 (series expansions after Theorem 11). -/
theorem kArndtCompositionCount_examples :
    kArndtCompositionCount 3 7 2 = 1 ∧ kArndtCompositionCount 3 7 3 = 1 ∧
      kArndtCompositionCount (-3) 4 2 = 3 := by
  decide

/-- **Generalized Arndt compositions.** For an integer $k$ and a natural number $n$, $a(n, k)$ is
the number of compositions $(c_1, \dots, c_m)$ of $n$, with any number $m \ge 0$ of parts, such
that $c_{2i-1} > c_{2i} + k$ for every $i$ with $2i \le m$; a final unpaired part is
unconstrained. The empty composition gives $a(0, k) = 1$, and $k = 0$ gives Arndt compositions.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Definition 4. -/
def kArndtTotalCount (k : ℤ) (n : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (n + 1), kArndtCompositionCount k n m

/-- **Generalized Arndt counts for compositions of five.** The numbers $a(5, k)$ of generalized
Arndt compositions of $5$ (compositions $(c_1, \dots, c_m)$ of $5$ with $c_{2i-1} > c_{2i} + k$
whenever $2i \le m$) are $a(5, 0) = 5$, $a(5, -1) = 10$, $a(5, -2) = 14$ and $a(5, 1) = 3$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Table 9. -/
theorem kArndtTotalCount_five :
    kArndtTotalCount 0 5 = 5 ∧ kArndtTotalCount (-1) 5 = 10 ∧ kArndtTotalCount (-2) 5 = 14 ∧
      kArndtTotalCount 1 5 = 3 := by
  decide

namespace kArndtTotalCount_recurrence

open Finset

private abbrev valid (k : ℤ) {m : ℕ} (c : Fin m → ℕ) :=
  (∀ i, 0 < c i) ∧ ∀ i j : Fin m, (i : ℕ) % 2 = 0 → (j : ℕ) = i + 1 → (c j : ℤ) + k < c i

private lemma valid_cons (k : ℤ) {m a b : ℕ} {c : Fin m → ℕ} :
    valid k (Fin.cons a (Fin.cons b c)) ↔
      0 < a ∧ 0 < b ∧ (b : ℤ) + k < a ∧ valid k c := by
  constructor
  · rintro ⟨hp, hd⟩
    refine ⟨hp 0, hp (Fin.succ 0), hd 0 (Fin.succ 0) rfl rfl, fun i ↦ hp i.succ.succ, ?_⟩
    intro i j hi hj
    apply hd i.succ.succ j.succ.succ <;> simp only [Fin.val_succ] <;> omega
  · rintro ⟨ha, hb, hba, hp, hd⟩
    constructor
    · exact Fin.cases ha (Fin.cases hb hp)
    · intro i
      refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun i ↦ ?_) i) i
      · intro j _ hj
        have : j = Fin.succ 0 := Fin.ext (by simpa using hj)
        simpa [this] using hba
      · simp
      · intro j
        refine Fin.cases (by simp) (fun j ↦ Fin.cases (by simp) (fun j ↦ ?_) j) j
        intro hi hj
        exact hd i j (by simp only [Fin.val_succ] at hi; omega)
          (by simp only [Fin.val_succ] at hj; omega)

-- For a pair of weight s, the second part b satisfies 1 ≤ b < s and 2b < s - k.
private def pairCount (k : ℤ) (s : ℕ) : ℕ :=
  min (s - 1) (((s : ℤ) - k - 1) / 2).toNat

private lemma lt_pairCount (k : ℤ) (s j : ℕ) :
    j < pairCount k s ↔ j + 1 < s ∧ ((j + 1 : ℕ) : ℤ) + k < (s - (j + 1) : ℕ) := by
  unfold pairCount
  omega

private lemma count_pair (k : ℤ) (n m : ℕ) :
    kArndtCompositionCount k n (m + 2) =
      ∑ p ∈ antidiagonal n, pairCount k p.1 * kArndtCompositionCount k p.2 m := by
  classical
  let tails (t : ℕ) := (Nat.antidiagonalTuple m t).filter (valid k)
  let pieces := (antidiagonal n).sigma fun p ↦ range (pairCount k p.1) ×ˢ tails p.2
  let join (z : Σ _ : ℕ × ℕ, ℕ × (Fin m → ℕ)) : Fin (m + 2) → ℕ :=
    Fin.cons (z.1.1 - (z.2.1 + 1)) (Fin.cons (z.2.1 + 1) z.2.2)
  let split (c : Fin (m + 2) → ℕ) : Σ _ : ℕ × ℕ, ℕ × (Fin m → ℕ) :=
    ⟨(c 0 + c (Fin.succ 0), ∑ i : Fin m, c i.succ.succ),
      c (Fin.succ 0) - 1, fun i ↦ c i.succ.succ⟩
  have mem_pieces (p : ℕ × ℕ) (j : ℕ) (c : Fin m → ℕ) :
      (⟨p, j, c⟩ : Σ _ : ℕ × ℕ, ℕ × (Fin m → ℕ)) ∈ pieces ↔
        p.1 + p.2 = n ∧ j < pairCount k p.1 ∧ (∑ i, c i) = p.2 ∧ valid k c := by
    simp [pieces, tails, Nat.mem_antidiagonalTuple]
  symm
  calc
    _ = pieces.card := by simp [pieces, tails, kArndtCompositionCount, valid, card_sigma]
    _ = _ := by
      change pieces.card = ((Nat.antidiagonalTuple (m + 2) n).filter (valid k)).card
      apply card_nbij' join split
      · rintro ⟨⟨s, t⟩, j, c⟩ hz
        obtain ⟨hst, hj, ht, hc⟩ := (mem_pieces _ _ _).mp hz
        obtain ⟨hj, hk⟩ := (lt_pairCount k s j).mp hj
        apply mem_filter.mpr
        simp only [Nat.mem_antidiagonalTuple, join, Fin.sum_cons, valid_cons]
        exact ⟨by dsimp at *; omega, by omega, by omega, hk, hc⟩
      · intro c hc
        obtain ⟨hs, hv⟩ := mem_filter.mp hc
        rw [Nat.mem_antidiagonalTuple, Fin.sum_univ_succ, Fin.sum_univ_succ] at hs
        have ha := hv.1 0
        have hb := hv.1 (Fin.succ 0)
        have hba := hv.2 0 (Fin.succ 0) rfl rfl
        change 0 < c 1 at hb
        change (c 1 : ℤ) + k < c 0 at hba
        change c 0 + (c 1 + ∑ i : Fin m, c i.succ.succ) = n at hs
        apply (mem_pieces _ _ _).mpr
        refine ⟨by dsimp; omega, (lt_pairCount _ _ _).mpr ?_, rfl, ?_⟩
        · change c 1 - 1 + 1 < c 0 + c 1 ∧ _
          dsimp [split]
          omega
        · exact ⟨fun i ↦ hv.1 i.succ.succ, fun i j hi hj ↦
            hv.2 i.succ.succ j.succ.succ (by simp; omega) (by simp; omega)⟩
      · rintro ⟨⟨s, t⟩, j, c⟩ hz
        obtain ⟨_, hj, ht, _⟩ := (mem_pieces _ _ _).mp hz
        have hj := ((lt_pairCount k s j).mp hj).1
        simp [split, join, ht, hj.le]
      · intro c hc
        have hb := (mem_filter.mp hc).2.1 (Fin.succ 0)
        change 0 < c 1 at hb
        funext i
        refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun _ ↦ rfl) i) i <;>
          simp [join, split] <;> omega

private lemma count_of_lt (k : ℤ) {n m : ℕ} (h : n < m) :
    kArndtCompositionCount k n m = 0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro c hc
  obtain ⟨hs, hp, _⟩ := mem_filter.mp hc
  have := sum_le_sum (s := univ) fun i _ ↦ (show 1 ≤ c i from hp i)
  simp [Nat.mem_antidiagonalTuple.mp hs] at this
  omega

private lemma total_eq_sum (k : ℤ) {n N : ℕ} (h : n ≤ N) :
    kArndtTotalCount k n = ∑ m ∈ range (N + 1), kArndtCompositionCount k n m := by
  apply sum_subset (range_mono (by omega))
  intro m _ hm
  exact count_of_lt k (by simpa using hm)

private lemma total_pair (k : ℤ) (n : ℕ) :
    kArndtTotalCount k n = 1 + ∑ p ∈ antidiagonal n, pairCount k p.1 * kArndtTotalCount k p.2 := by
  have short : kArndtCompositionCount k n 0 + kArndtCompositionCount k n 1 = 1 := by
    cases n <;> simp [kArndtCompositionCount, Fin.forall_fin_one, filter_singleton]
  rw [total_eq_sum k (N := n + 2) (by omega), show n + 2 + 1 = 2 + (n + 1) by omega,
    sum_range_add, sum_range_succ, sum_range_succ, sum_range_zero, zero_add, short]
  congr 1
  simp_rw [Nat.add_comm 2, count_pair]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [total_eq_sum k (N := n) (by have := mem_antidiagonal.mp hp; omega), mul_sum]

open PowerSeries

private noncomputable def totalSeries (k : ℤ) : PowerSeries ℤ :=
  mk fun n ↦ (kArndtTotalCount k n : ℤ)

private noncomputable def pairSeries (k : ℤ) : PowerSeries ℤ :=
  mk fun n ↦ (pairCount k n : ℤ)

-- The empty composition and the singletons together contribute one at every weight.
private noncomputable def shortSeries : PowerSeries ℤ := mk fun _ ↦ 1

private lemma decompose (k : ℤ) :
    totalSeries k = shortSeries + totalSeries k * pairSeries k := by
  apply PowerSeries.ext
  intro n
  rw [mul_comm]
  simpa [totalSeries, shortSeries, pairSeries, coeff_mul] using
    congrArg (fun a : ℕ ↦ (a : ℤ)) (total_pair k n)

private lemma short_mul : shortSeries * (1 - X) = 1 := by
  ext n
  cases n <;> simp [mul_sub, shortSeries, coeff_one, coeff_succ_mul_X]

-- Removing one from both parts cancels the pairs whose two parts exceed one.
-- At weight n+2 the boundary pairs are (n+1,1) and, when n>0, (1,n+1).
private lemma pair_diff (k : ℤ) (n : ℕ) :
    (pairCount k (n + 2) : ℤ) - pairCount k n =
      (if k < (n : ℤ) then 1 else 0) + (if 0 < n ∧ (n : ℤ) + k < 0 then 1 else 0) := by
  unfold pairCount
  split_ifs <;> omega

private lemma pair_mul (k : ℤ) :
    pairSeries k * ((1 - X) * (1 - X ^ 2)) =
      if 0 ≤ k then X ^ (k.toNat + 3)
      else X ^ 2 + X ^ 3 - X ^ ((-k).toNat + 2) := by
  rw [show pairSeries k * ((1 - X) * (1 - X ^ 2)) = (pairSeries k - pairSeries k * X ^ 2) -
    (pairSeries k - pairSeries k * X ^ 2) * X by ring]
  apply PowerSeries.ext
  intro n
  rcases n with _ | _ | _ | n
  · split_ifs <;> simp [map_sub, coeff_mul_X_pow', coeff_X_pow, pairSeries, pairCount]
  · split_ifs <;> simp [map_sub, coeff_succ_mul_X, coeff_mul_X_pow', coeff_X_pow,
      pairSeries, pairCount]
  · split_ifs <;> simp [map_sub, coeff_succ_mul_X, coeff_mul_X_pow', coeff_X_pow,
      pairSeries, pairCount] <;> omega
  · simp only [map_sub, coeff_succ_mul_X]
    rw [coeff_mul_X_pow (pairSeries k) 2 (n + 1), coeff_mul_X_pow (pairSeries k) 2 n]
    simp only [pairSeries, coeff_mk]
    change (pairCount k (n + 1 + 2) : ℤ) - pairCount k (n + 1) -
      ((pairCount k (n + 2) : ℤ) - pairCount k n) = _
    rw [pair_diff, pair_diff]
    split_ifs <;> simp only [map_sub, map_add, coeff_X_pow] <;> split_ifs <;> omega

-- Clear the denominator of the first-pair decomposition before extracting coefficients.
private lemma total_mul (k : ℤ) :
    totalSeries k - totalSeries k * X ^ 1 - totalSeries k * X ^ 2 + totalSeries k * X ^ 3 =
      1 - X ^ 2 + totalSeries k * (pairSeries k * ((1 - X) * (1 - X ^ 2))) := by
  linear_combination ((1 - X) * (1 - X ^ 2)) * decompose k + (1 - X ^ 2) * short_mul

private lemma coeff_total_mul (k : ℤ) (n : ℕ) (hn : 3 ≤ n) :
    (kArndtTotalCount k n : ℤ) - kArndtTotalCount k (n - 1) - kArndtTotalCount k (n - 2) +
      kArndtTotalCount k (n - 3) =
        coeff n (totalSeries k * (pairSeries k * ((1 - X) * (1 - X ^ 2)))) := by
  have e := congrArg (coeff (R := ℤ) n) (total_mul k)
  simpa only [map_sub, map_add, coeff_mul_X_pow', coeff_one, coeff_X_pow, totalSeries,
    coeff_mk, ite_eq_left hn, ite_eq_left (show 1 ≤ n by omega), ite_eq_left (show 2 ≤ n by omega),
    ite_eq_right (show n ≠ 0 by omega), ite_eq_right (show n ≠ 2 by omega), sub_zero,
    zero_add] using e

private lemma pair_mul_neg (j : ℕ) :
    pairSeries (-(j : ℤ)) * ((1 - X) * (1 - X ^ 2)) =
      X ^ 2 + X ^ 3 - X ^ (j + 2) := by
  rw [pair_mul]
  cases j with
  | zero => simp
  | succ j => rw [ite_eq_right (by omega), neg_neg, Int.toNat_natCast]

end kArndtTotalCount_recurrence

open kArndtTotalCount_recurrence PowerSeries in
/-- **Recurrences for generalized Arndt counts.** Let $a(n, k)$ be the number of generalized
Arndt compositions of $n$ with shift $k$, set $a(m, k) = 0$ for $m < 0$, and note that
$a(0, k) = 1$ counts the empty composition. For every natural number $j$ and every $n \ge 3$,
$$a(n, -j) = a(n - 1, -j) + 2a(n - 2, -j) - a(n - 2 - j, -j),$$
and for every natural number $k$ and every $n \ge 3$,
$$a(n, k) = a(n - 1, k) + a(n - 2, k) - a(n - 3, k) + a(n - 3 - k, k).$$

The paper sets $a(n - 2 - j, -j) = 0$ whenever $n - 2 - j \le 0$; at $n - 2 - j = 0$ that is
false ($j = 1$, $n = 3$: $a(3, -1) = 3$, while $a(2, -1) + 2a(1, -1) - 0 = 4$), and its own
bijection uses the empty composition there. At $n = 2$ the recurrences fail for every shift
(for instance $a(2, k) \ne a(1, k) + 2a(0, k)$), so $n \ge 3$ is assumed.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Theorem 4 (`integers-2026-A64-thm-4`). -/
theorem kArndtTotalCount_recurrence :
    (∀ j n : ℕ, 3 ≤ n →
      (kArndtTotalCount (-(j : ℤ)) n : ℤ) =
        kArndtTotalCount (-(j : ℤ)) (n - 1) + 2 * kArndtTotalCount (-(j : ℤ)) (n - 2) -
          if j + 2 ≤ n then (kArndtTotalCount (-(j : ℤ)) (n - 2 - j) : ℤ) else 0) ∧
    ∀ k n : ℕ, 3 ≤ n →
      (kArndtTotalCount k n : ℤ) =
        kArndtTotalCount k (n - 1) + kArndtTotalCount k (n - 2) - kArndtTotalCount k (n - 3) +
          if k + 3 ≤ n then (kArndtTotalCount k (n - 3 - k) : ℤ) else 0 := by
  constructor
  · intro j n hn
    have h := coeff_total_mul (-(j : ℤ)) n hn
    rw [pair_mul_neg, mul_sub, mul_add, map_sub, map_add] at h
    simp only [coeff_mul_X_pow', ite_eq_left hn, ite_eq_left (show 2 ≤ n by omega), totalSeries,
      coeff_mk] at h
    rw [Nat.sub_sub, Nat.add_comm 2 j]
    omega
  · intro k n hn
    have h := coeff_total_mul (k : ℤ) n hn
    rw [pair_mul, ite_eq_left (by omega), Int.toNat_natCast, coeff_mul_X_pow'] at h
    simp only [totalSeries, coeff_mk] at h
    rw [Nat.sub_sub, Nat.add_comm 3 k]
    omega

end

end MetaMathlibExt
