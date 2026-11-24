/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Generating function of colored Arndt compositions

We prove the closed form of the bivariate generating function by removing the initial
descending pair and counting the independent color choices for its two parts.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Colored Arndt compositions.** An Arndt composition of $n$ with $k$ parts is a sequence
$(\sigma_1, \dots, \sigma_k)$ of positive integers with sum $n$ such that
$\sigma_{2i-1} > \sigma_{2i}$ for every $i$ with $2i \le k$. In a colored Arndt composition, each
part of size $m$ carries one of $m$ colors. The number $c(n, k)$ of colored Arndt compositions of
$n$ with $k$ parts is therefore the sum of $\sigma_1 \sigma_2 \cdots \sigma_k$ over all Arndt
compositions $(\sigma_1, \dots, \sigma_k)$ of $n$ with $k$ parts.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 4 (definition of colored Arndt compositions). -/
def coloredArndtCount (n k : ℕ) : ℕ :=
  ∑ c ∈ (Finset.Nat.antidiagonalTuple k n).filter (fun c =>
      (∀ i, 0 < c i) ∧ ∀ i j : Fin k, (i : ℕ) % 2 = 0 → (j : ℕ) = i + 1 → c j < c i),
    ∏ i, c i

/-- **Colored Arndt compositions of 4.** Write $m_a$ for a part of size $m$ with color
$a \in \{1, \dots, m\}$. The colored Arndt compositions of $4$ are $(4_1)$, $(4_2)$, $(4_3)$,
$(4_4)$, $(3_a, 1_1)$ for $a \le 3$, and $(2_a, 1_1, 1_1)$ for $a \le 2$. Hence the numbers of
colored Arndt compositions of $4$ with $1$, $2$ and $3$ parts are $c(4, 1) = 4$, $c(4, 2) = 3$
and $c(4, 3) = 2$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 4, list (6). -/
theorem coloredArndtCount_four : coloredArndtCount 4 1 = 4 ∧ coloredArndtCount 4 2 = 3 ∧
    coloredArndtCount 4 3 = 2 := by
  decide

/-- **Generating function of colored Arndt compositions.** The bivariate generating function of
colored Arndt compositions, by weight ($x$) and number of parts ($y$), is the power series
$C(x, y) = \sum_{n \ge 0} \left(\sum_{k=0}^{n} c(n, k)\, y^k\right) x^n$ in $\mathbb{Z}[y][[x]]$,
where $c(n, k)$ is the number of colored Arndt compositions of $n$ with $k$ parts.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 4 (definition of `C(x, y)`). -/
noncomputable def coloredArndtGF : PowerSeries (Polynomial ℤ) :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), (coloredArndtCount n k : Polynomial ℤ) * Polynomial.X ^ k

namespace coloredArndtGF_mul

open Finset

private abbrev valid {k : ℕ} (c : Fin k → ℕ) :=
  (∀ i, 0 < c i) ∧ ∀ i j : Fin k, (i : ℕ) % 2 = 0 → (j : ℕ) = i + 1 → c j < c i

private lemma valid_cons {k a b : ℕ} {c : Fin k → ℕ} :
    valid (Fin.cons a (Fin.cons b c)) ↔ 0 < b ∧ b < a ∧ valid c := by
  constructor
  · rintro ⟨hp, hd⟩
    refine ⟨hp (Fin.succ 0), hd 0 (Fin.succ 0) rfl rfl, fun i ↦ hp i.succ.succ, ?_⟩
    intro i j hi hj
    apply hd i.succ.succ j.succ.succ <;> simp only [Fin.val_succ] <;> omega
  · rintro ⟨hb, hba, hp, hd⟩
    constructor
    · intro i
      refine Fin.cases (by simpa using hb.trans hba) (fun i ↦ ?_) i
      exact Fin.cases hb hp i
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

-- The smaller part of a pair of weight n runs from 1 through ⌊(n − 1)/2⌋.
private def pairWeight (n : ℕ) : ℕ :=
  ∑ j ∈ range ((n - 1) / 2), (n - (j + 1)) * (j + 1)

private lemma count_pair (n k : ℕ) :
    coloredArndtCount n (k + 2) =
      ∑ p ∈ antidiagonal n, pairWeight p.1 * coloredArndtCount p.2 k := by
  classical
  let tails (t : ℕ) := (Nat.antidiagonalTuple k t).filter valid
  let pieces := (antidiagonal n).sigma fun p ↦ range ((p.1 - 1) / 2) ×ˢ tails p.2
  let join (z : Σ _ : ℕ × ℕ, ℕ × (Fin k → ℕ)) : Fin (k + 2) → ℕ :=
    Fin.cons (z.1.1 - (z.2.1 + 1)) (Fin.cons (z.2.1 + 1) z.2.2)
  let split (c : Fin (k + 2) → ℕ) : Σ _ : ℕ × ℕ, ℕ × (Fin k → ℕ) :=
    ⟨(c 0 + c (Fin.succ 0), ∑ i : Fin k, c i.succ.succ),
      c (Fin.succ 0) - 1, fun i ↦ c i.succ.succ⟩
  have mem_pieces (p : ℕ × ℕ) (j : ℕ) (c : Fin k → ℕ) :
      (⟨p, j, c⟩ : Σ _ : ℕ × ℕ, ℕ × (Fin k → ℕ)) ∈ pieces ↔
        p.1 + p.2 = n ∧ j < (p.1 - 1) / 2 ∧ (∑ i, c i) = p.2 ∧ valid c := by
    simp [pieces, tails, Nat.mem_antidiagonalTuple]
  change (∑ c ∈ (Nat.antidiagonalTuple (k + 2) n).filter valid, ∏ i, c i) = _
  symm
  calc
    _ = ∑ z ∈ pieces, (z.1.1 - (z.2.1 + 1)) * (z.2.1 + 1) * ∏ i, z.2.2 i := by
      rw [sum_sigma]
      apply sum_congr rfl
      rintro ⟨s, t⟩ _
      simp only [pairWeight, coloredArndtCount, tails, valid, sum_product, sum_mul, mul_sum]
      exact sum_comm
    _ = _ := by
      apply sum_nbij' join split
      · rintro ⟨⟨s, t⟩, j, c⟩ hz
        obtain ⟨hst, hj, ht, hc⟩ := (mem_pieces _ _ _).mp hz
        simp only [mem_filter, Nat.mem_antidiagonalTuple, join, Fin.sum_cons, valid_cons]
        dsimp at *
        exact ⟨by omega, by omega, by omega, hc⟩
      · intro c hc
        obtain ⟨hs, hv⟩ := mem_filter.mp hc
        rw [Nat.mem_antidiagonalTuple, Fin.sum_univ_succ, Fin.sum_univ_succ] at hs
        have hb := hv.1 (Fin.succ 0)
        have hba := hv.2 0 (Fin.succ 0) rfl rfl
        change 0 < c 1 at hb
        change c 1 < c 0 at hba
        change c 0 + (c 1 + ∑ i : Fin k, c i.succ.succ) = n at hs
        apply (mem_pieces _ _ _).mpr
        refine ⟨by dsimp; omega, by dsimp; omega, rfl, ?_⟩
        exact ⟨fun i ↦ hv.1 i.succ.succ, fun i j hi hj ↦
          hv.2 i.succ.succ j.succ.succ (by simp; omega) (by simp; omega)⟩
      · rintro ⟨⟨s, t⟩, j, c⟩ hz
        obtain ⟨_, hj, ht, _⟩ := (mem_pieces _ _ _).mp hz
        simp [split, join, ht, show j + 1 ≤ s by dsimp at hj; omega]
      · intro c hc
        have hb := (mem_filter.mp hc).2.1 (Fin.succ 0)
        change 0 < c 1 at hb
        funext i
        refine Fin.cases ?_ (fun i ↦ Fin.cases ?_ (fun _ ↦ rfl) i) i <;>
          simp [join, split] <;> omega
      · rintro ⟨⟨s, t⟩, j, c⟩ _
        simp [join, Fin.prod_cons, mul_assoc]

private lemma count_zero (n : ℕ) : coloredArndtCount n 0 = if n = 0 then 1 else 0 := by
  cases n <;> simp [coloredArndtCount]

private lemma count_one (n : ℕ) : coloredArndtCount n 1 = n := by
  cases n <;> simp [coloredArndtCount, Nat.antidiagonalTuple_one, Fin.forall_fin_one,
    filter_singleton]

private lemma count_of_lt {n k : ℕ} (h : n < k) : coloredArndtCount n k = 0 := by
  apply sum_eq_zero
  intro c hc
  obtain ⟨hs, hp, _⟩ := mem_filter.mp hc
  have := sum_le_sum (s := univ) fun i _ ↦ (show 1 ≤ c i from hp i)
  simp [Nat.mem_antidiagonalTuple.mp hs] at this
  omega

open PowerSeries

private abbrev Series := PowerSeries (Polynomial ℤ)

private noncomputable def singleSeries : Series := mk fun n ↦ (n : Polynomial ℤ)

private noncomputable def pairSeries : Series := mk fun n ↦ (pairWeight n : Polynomial ℤ)

private lemma coeff_count (n k : ℕ) :
    ((coeff n) coloredArndtGF).coeff k = coloredArndtCount n k := by
  simp only [coloredArndtGF, coeff_mk, Polynomial.finsetSum_coeff, Polynomial.coeff_natCast_mul,
    Polynomial.coeff_X_pow, mul_boole, sum_ite_eq, mem_range]
  split_ifs with h
  · rfl
  · rw [count_of_lt (by omega), Nat.cast_zero]

-- Every composition is empty, has a single part, or starts with a descending pair.
private lemma decompose :
    coloredArndtGF = 1 + singleSeries * C Polynomial.X +
      (pairSeries * coloredArndtGF) * C (Polynomial.X ^ 2) := by
  apply PowerSeries.ext
  intro n
  ext k
  have h : (coeff n (1 : Series)).coeff k = (if n = 0 ∧ k = 0 then 1 else 0) := by
    by_cases hn : n = 0 <;> simp [coeff_one, hn, Polynomial.coeff_one]
  simp only [coeff_count, map_add, h, coeff_mul_C, singleSeries, coeff_mk,
    Polynomial.coeff_add, Polynomial.coeff_natCast_mul, Polynomial.coeff_X]
  cases k with
  | zero =>
    simp [count_zero]
  | succ k =>
    cases k with
    | zero => simp [count_one, Polynomial.coeff_mul_X_pow']
    | succ k =>
      simp [count_pair, Polynomial.coeff_mul_X_pow, coeff_mul, pairSeries,
        Polynomial.coeff_natCast_mul, coeff_count]

private lemma single_mul : singleSeries * (1 - X) ^ 2 = X := by
  rw [show singleSeries * (1 - X) ^ 2 =
    singleSeries - 2 * (singleSeries * X ^ 1) + singleSeries * X ^ 2 by ring]
  apply PowerSeries.ext
  intro n
  rcases n with _ | _ | n
  all_goals simp [coeff_mul_X_pow', coeff_X, singleSeries]
  ring

-- Increasing both parts by one adds n + 1 color choices to a pair of weight n.
-- The new pair with smaller part one contributes another n + 1 choices.
private lemma pairWeight_step (n : ℕ) :
    pairWeight (n + 2) = pairWeight n + (n + 1) * ((n + 1) / 2) := by
  cases n with
  | zero => decide
  | succ n =>
    have step (j : ℕ) (hj : j ∈ range (n / 2)) :
        (n + 3 - (j + 1 + 1)) * (j + 1 + 1) =
          (n + 1 - (j + 1)) * (j + 1) + (n + 2) := by
      rw [mem_range] at hj
      rw [show n + 3 - (j + 1 + 1) = n + 1 - (j + 1) + 1 by omega]
      have : n + 1 - (j + 1) + (j + 1) = n + 1 := by omega
      nlinarith only [this]
    unfold pairWeight
    rw [show (n + 1 + 2 - 1) / 2 = n / 2 + 1 by omega, sum_range_succ',
      sum_congr rfl step, sum_add_distrib]
    simp [show (n + 1 + 1) / 2 = n / 2 + 1 by omega]
    ring

private lemma pair_expand :
    pairSeries * (1 - X ^ 2) ^ 3 =
      pairSeries - 3 * (pairSeries * X ^ 2) + 3 * (pairSeries * X ^ 4) -
        pairSeries * X ^ 6 := by ring

-- The third difference with step two is constant.
private lemma coeff_pair_diff (n : ℕ) :
    coeff (n + 6) (pairSeries * (1 - X ^ 2) ^ 3) = 4 := by
  rw [pair_expand]
  simp only [map_sub, map_add, coeff_ofNat_mul]
  rw [coeff_mul_X_pow pairSeries 2 (n + 4), coeff_mul_X_pow pairSeries 4 (n + 2),
    coeff_mul_X_pow pairSeries 6 n]
  simp only [pairSeries, coeff_mk]
  rw [pairWeight_step (n + 4), pairWeight_step (n + 2), pairWeight_step n,
    show (n + 4 + 1) / 2 = (n + 1) / 2 + 2 by omega,
    show (n + 2 + 1) / 2 = (n + 1) / 2 + 1 by omega]
  push_cast
  ring

private lemma pair_mul :
    pairSeries * ((1 - X) ^ 4 * (1 + X) ^ 3) = X ^ 3 * (2 + X + X ^ 2) := by
  rw [show (1 - X : Series) ^ 4 * (1 + X) ^ 3 = (1 - X ^ 2) ^ 3 * (1 - X) by ring,
    ← mul_assoc, mul_sub, mul_one,
    show (X : Series) ^ 3 * (2 + X + X ^ 2) = 2 * X ^ 3 + X ^ 4 + X ^ 5 by ring]
  apply PowerSeries.ext
  intro n
  by_cases hn : 7 ≤ n
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [map_sub, coeff_succ_mul_X, coeff_pair_diff (m + 1), coeff_pair_diff m]
    simp [coeff_X_pow]
  · rw [pair_expand]
    interval_cases n <;>
      norm_num [coeff_mul_X_pow', coeff_X_pow, pairSeries,
        pairWeight, sum_range_succ]

end coloredArndtGF_mul

open PowerSeries coloredArndtGF_mul

/-- **Closed form of the generating function of colored Arndt compositions.** Let
$C(x, y) = \sum_{n, k} c(n, k)\, x^n y^k$ in $\mathbb{Z}[y][[x]]$, where $c(n, k)$ is the number
of colored Arndt compositions of $n$ with $k$ parts. Then
$C(x, y) \cdot (1 - x - 3x^2 - x^3(2y^2 - 3) - x^4(y^2 - 3) - x^5(3 + y^2) - x^6 + x^7) =
(1 - x)^2 (1 + x)^3 (1 + x^2 + x(y - 2))$.

Since the second factor on the left has constant term $1$, this says that
$C(x, y) = \frac{(1 - x)^2 (1 + x)^3 (1 + x^2 + x(y - 2))}{1 - x - 3x^2 - x^3(2y^2 - 3) -
x^4(y^2 - 3) - x^5(3 + y^2) - x^6 + x^7}$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Theorem 17 (`jis-2025-25.3.6-thm-17`). -/
public theorem coloredArndtGF_mul :
    coloredArndtGF *
        (1 - PowerSeries.X - 3 * PowerSeries.X ^ 2 -
          PowerSeries.X ^ 3 * (2 * PowerSeries.C (Polynomial.X ^ 2) - 3) -
          PowerSeries.X ^ 4 * (PowerSeries.C (Polynomial.X ^ 2) - 3) -
          PowerSeries.X ^ 5 * (3 + PowerSeries.C (Polynomial.X ^ 2)) -
          PowerSeries.X ^ 6 + PowerSeries.X ^ 7) =
      (1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) ^ 3 *
        (1 + PowerSeries.X ^ 2 + PowerSeries.X * (PowerSeries.C Polynomial.X - 2)) := by
  have h := decompose
  rw [map_pow] at h ⊢
  linear_combination
    (1 - X) ^ 4 * (1 + X) ^ 3 * h + coloredArndtGF * C Polynomial.X ^ 2 * pair_mul +
      C Polynomial.X * (1 - X) ^ 2 * (1 + X) ^ 3 * single_mul

end

end MetaMathlibExt
