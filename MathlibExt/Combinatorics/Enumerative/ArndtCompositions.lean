/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Bounds
import MathlibExt.Combinatorics.Enumerative.KArndtRecurrence
import MathlibExt.Data.Nat.Choose.HockeyStickConvolution

/-!
# Arndt compositions with a fixed number of parts

We define the number `a_S(n, k)` of Arndt compositions of `n` with `k` parts in a set `S`, and
prove that for every fixed `m ≥ 1` the number `a(n, m)` of Arndt compositions of `n` with `m`
parts satisfies `a(n, m) ∼ n^(m-1) / (2^⌊m/2⌋ (m-1)!)` as `n → ∞`
(`MetaMathlibExt.arndtCompositionCount_isEquivalent`; D. F. Checa and J. L. Ramírez,
arXiv:2311.15388v1, Corollary 2.5, where it follows from the generating function by a transfer
theorem).

The proof here is elementary. Removing the leading descending pair, as in
`MathlibExt/Combinatorics/Enumerative/ColoredArndt.lean`, gives
`a(n, m + 2) = ∑_{s + t = n} ⌊(s - 1)/2⌋ a(t, m)`. For `n ≥ 1`, the number `C(n - 1, m - 1)` of
compositions of `n` into `m` positive parts satisfies the same recursion with weight `s - 1`
(the hockey-stick convolution `Nat.sum_antidiagonal_choose_mul_choose`). By induction on `m`,
`2^⌊m/2⌋ a(n, m)` lies between `C(n - 1, m - 1) - ⌊m/2⌋ (n + 1)^(m-2)` and `C(n - 1, m - 1)`, and
`C(n - 1, m - 1) ∼ n^(m-1)/(m-1)!` by Mathlib's `isEquivalent_choose`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Number of Arndt compositions with parts in a set.** For a set $S$ of natural numbers and
natural numbers $n$ and $k$, $a_S(n, k)$ is the number of $k$-tuples $(c_1, \dots, c_k)$ of
positive integers such that $c_1 + \dots + c_k = n$, every $c_i$ lies in $S$, and
$c_{2i-1} > c_{2i}$ for every $i$ with $2i \le k$. These tuples are the Arndt compositions of
$n$ with $k$ parts in $S$.

Source: Mohammed L. Nadji, Moussa Ahmia, Daniel F. Checa, and José L. Ramírez, *Arndt
Compositions with Restricted Parts, Palindromes, and Colored Variants*, Journal of Integer
Sequences 28 (2025), Article 25.3.6, Section 1 (definition of Arndt compositions, after
D. F. Checa and J. L. Ramírez, arXiv:2311.15388, Section 1). -/
def arndtCompositionCount (S : ℕ → Prop) [DecidablePred S] (n k : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple k n).filter fun c =>
    (∀ i, 0 < c i ∧ S (c i)) ∧
      ∀ i j : Fin k, (i : ℕ) % 2 = 0 → (j : ℕ) = i + 1 → c j < c i).card

/-- **Arndt compositions of 6 with two parts.** There are exactly $2$ Arndt compositions of $6$
with two parts.

They are $(5, 1)$ and $(4, 2)$.

Source: D. F. Checa and J. L. Ramírez, *Arndt compositions: a generating functions approach*,
arXiv:2311.15388, Section 1 (list of the Arndt compositions of `6`). -/
theorem arndtCompositionCount_six_two : arndtCompositionCount (fun _ => True) 6 2 = 2 := by
  decide

/-- **Arndt compositions of 6 with three parts.** There are exactly $4$ Arndt compositions of $6$
with three parts.

They are $(4, 1, 1)$, $(3, 2, 1)$, $(3, 1, 2)$ and $(2, 1, 3)$.

Source: D. F. Checa and J. L. Ramírez, *Arndt compositions: a generating functions approach*,
arXiv:2311.15388, Section 1 (list of the Arndt compositions of `6`). -/
theorem arndtCompositionCount_six_three : arndtCompositionCount (fun _ => True) 6 3 = 4 := by
  decide

/-- **Arndt compositions of 6 with four parts.** There is exactly one Arndt composition of $6$
with four parts.

It is $(2, 1, 2, 1)$.

Source: D. F. Checa and J. L. Ramírez, *Arndt compositions: a generating functions approach*,
arXiv:2311.15388, Section 1 (list of the Arndt compositions of `6`). -/
theorem arndtCompositionCount_six_four : arndtCompositionCount (fun _ => True) 6 4 = 1 := by
  decide

open PowerSeries in
/-- **Arndt compositions are counted by Fibonacci numbers.** Let $a(n, m)$ be the number of Arndt
compositions of $n$ with $m$ parts, let $a(n) = \sum_{m=0}^{n} a(n, m)$ be the number of all
Arndt compositions of $n$, and let $F_n$ be the $n$-th Fibonacci number ($F_0 = 0$, $F_1 = 1$).
Then, in $\mathbb{Z}[[x]]$,
$$\Big(\sum_{n \ge 0} a(n) x^n\Big)(1 - x - x^2) = 1 - x^2,$$
and $a(n) = F_n$ for every $n \ge 1$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Corollary 2 (`integers-2024-A35-cor-2`). -/
theorem arndtComposition_total_eq_fib :
    (PowerSeries.mk fun n =>
        ((∑ m ∈ Finset.range (n + 1), arndtCompositionCount (fun _ => True) n m : ℕ) : ℤ)) *
        (1 - PowerSeries.X - PowerSeries.X ^ 2) = 1 - PowerSeries.X ^ 2 ∧
      ∀ n : ℕ, 1 ≤ n →
        ∑ m ∈ Finset.range (n + 1), arndtCompositionCount (fun _ => True) n m = Nat.fib n := by
  let a (n : ℕ) : ℕ := ∑ m ∈ Finset.range (n + 1), arndtCompositionCount (fun _ => True) n m
  change (mk fun n => (a n : ℤ)) * (1 - X - X ^ 2) = 1 - X ^ 2 ∧
    ∀ n : ℕ, 1 ≤ n → a n = Nat.fib n
  have hcount (n m : ℕ) :
      arndtCompositionCount (fun _ => True) n m = kArndtCompositionCount 0 n m := by
    unfold arndtCompositionCount kArndtCompositionCount
    congr 1
    exact Finset.filter_congr fun c _ => by simp
  have htotal (n : ℕ) : a n = kArndtTotalCount 0 n := by
    simp only [a, kArndtTotalCount, hcount]
  -- At shift zero the two terms at weight `n - 3` cancel.
  have hstep (n : ℕ) : (a (n + 3) : ℤ) = (a (n + 2) : ℤ) + (a (n + 1) : ℤ) := by
    have hn : 3 ≤ n + 3 := by omega
    simpa only [Nat.cast_zero, zero_add, ite_eq_left hn, Nat.sub_zero, sub_add_cancel,
      show n + 3 - 1 = n + 2 by omega, show n + 3 - 2 = n + 1 by omega, ← htotal] using
      kArndtTotalCount_recurrence.2 0 (n + 3) hn
  have h0 : a 0 = 1 := by decide
  have h1 : a 1 = 1 := by decide
  have h2 : a 2 = 1 := by decide
  constructor
  · apply PowerSeries.ext
    intro n
    simp only [mul_sub, mul_one, map_sub, coeff_mk, coeff_mul_X_pow', coeff_one, coeff_X_pow]
    rcases n with _ | _ | _ | n
    · simp [h0, coeff_zero_mul_X]
    · simp [h0, h1, coeff_succ_mul_X]
    · simp [h0, h1, h2, coeff_succ_mul_X]
    · have h : (a (n + 3) : ℤ) - a (n + 2) - a (n + 1) = 0 := by
        rw [hstep n]
        omega
      simpa [coeff_succ_mul_X] using h
  · intro n hn
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      rcases n with _ | _ | _ | n
      · omega
      · simpa using h1
      · simpa using h2
      · have h : a (n + 3) = a (n + 2) + a (n + 1) := by
          exact_mod_cast hstep n
        rw [h, ih (n + 2) (by omega) (by omega), ih (n + 1) (by omega) (by omega),
          Nat.fib_add_two (n := n + 1), Nat.add_comm]

namespace arndtCompositionCount_isEquivalent

open Finset

private abbrev valid {k : ℕ} (c : Fin k → ℕ) :=
  (∀ i, 0 < c i) ∧ ∀ i j : Fin k, (i : ℕ) % 2 = 0 → (j : ℕ) = i + 1 → c j < c i

private lemma count_eq (n k : ℕ) :
    arndtCompositionCount (fun _ => True) n k =
      ((Nat.antidiagonalTuple k n).filter valid).card := by
  unfold arndtCompositionCount
  congr 1
  exact filter_congr fun c _ => by simp [valid]

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

-- Removing the leading descending pair `(s - j - 1, j + 1)`, `j < ⌊(s - 1)/2⌋`, of weight `s`.
-- `valid_cons` and this bijection follow the private lemmas of the same names in
-- `MathlibExt/Combinatorics/Enumerative/ColoredArndt.lean`, which count weighted compositions.
private lemma count_pair (n k : ℕ) :
    arndtCompositionCount (fun _ => True) n (k + 2) =
      ∑ p ∈ antidiagonal n, (p.1 - 1) / 2 * arndtCompositionCount (fun _ => True) p.2 k := by
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
  have hcard : pieces.card =
      ∑ p ∈ antidiagonal n, (p.1 - 1) / 2 * arndtCompositionCount (fun _ => True) p.2 k := by
    simp only [pieces, card_sigma, card_product, card_range, count_eq, tails]
  rw [← hcard, count_eq]
  symm
  apply card_nbij' join split
  · rintro ⟨⟨s, t⟩, j, c⟩ hz
    obtain ⟨hst, hj, ht, hc⟩ := (mem_pieces _ _ _).mp hz
    simp only [mem_coe, mem_filter, Nat.mem_antidiagonalTuple, join, Fin.sum_cons, valid_cons]
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

private lemma count_zero (n : ℕ) :
    arndtCompositionCount (fun _ => True) n 0 = if n = 0 then 1 else 0 := by
  cases n <;> simp [arndtCompositionCount]

private lemma count_one (n : ℕ) :
    arndtCompositionCount (fun _ => True) n 1 = if n = 0 then 0 else 1 := by
  cases n <;> simp [arndtCompositionCount, Nat.antidiagonalTuple_one, Fin.forall_fin_one,
    filter_singleton]

private lemma count_two (n : ℕ) : arndtCompositionCount (fun _ => True) n 2 = (n - 1) / 2 := by
  rw [count_pair, sum_eq_single (n, 0)]
  · simp [count_zero]
  · rintro ⟨s, t⟩ hp hne
    have ht : t ≠ 0 := by
      rintro rfl
      simp only [mem_antidiagonal, add_zero] at hp
      exact hne (by rw [hp])
    simp [count_zero, ht]
  · simp

-- The number of compositions of `n` into `m ≥ 1` positive parts.
private def freeCount (n m : ℕ) : ℕ := if n = 0 then 0 else (n - 1).choose (m - 1)

-- Compositions satisfy the pair recursion with weight `s - 1`.
private lemma freeCount_pair {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    ∑ p ∈ antidiagonal n, (p.1 - 1) * freeCount p.2 m = freeCount n (m + 2) := by
  rcases n with _ | _ | N
  · simp [freeCount]
  · simp [freeCount, Nat.sum_antidiagonal_succ]
  · have key := Nat.sum_antidiagonal_choose_mul_choose N 1 (m - 1)
    simp only [Nat.choose_one_right] at key
    rw [show 1 + (m - 1) + 1 = m + 1 by omega] at key
    rw [Nat.sum_antidiagonal_succ', Nat.sum_antidiagonal_succ]
    simp [freeCount, key]

private lemma freeCount_le {m t n : ℕ} (htn : t ≤ n) : freeCount t m ≤ (n + 1) ^ (m - 1) := by
  unfold freeCount
  split_ifs
  · exact Nat.zero_le _
  · exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)

-- `2^⌊m/2⌋ a(n, m)` lies between `C(n - 1, m - 1) - ⌊m/2⌋ (n + 1)^(m-2)` and `C(n - 1, m - 1)`.
private def Bounds (m : ℕ) : Prop :=
  ∀ n, 2 ^ (m / 2) * arndtCompositionCount (fun _ => True) n m ≤ freeCount n m ∧
    freeCount n m ≤
      2 ^ (m / 2) * arndtCompositionCount (fun _ => True) n m + m / 2 * (n + 1) ^ (m - 2)

private lemma bounds_one : Bounds 1 := by
  intro n
  rcases n with _ | n <;> simp [freeCount, count_one]

private lemma bounds_two : Bounds 2 := by
  intro n
  rcases n with _ | n
  · simp [count_two, freeCount]
  · simp only [count_two, freeCount, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
      Nat.reduceSub, Nat.choose_one_right, pow_zero]
    omega

private lemma bounds_step {m : ℕ} (hm : 1 ≤ m) (ih : Bounds m) : Bounds (m + 2) := by
  intro n
  have hH : (m + 2) / 2 = m / 2 + 1 := by omega
  rw [hH, count_pair, ← freeCount_pair hm, mul_sum, pow_succ]
  constructor
  · apply sum_le_sum
    intro p _
    calc 2 ^ (m / 2) * 2 * ((p.1 - 1) / 2 * arndtCompositionCount (fun _ => True) p.2 m)
        = 2 * ((p.1 - 1) / 2) * (2 ^ (m / 2) * arndtCompositionCount (fun _ => True) p.2 m) := by
          ring
      _ ≤ (p.1 - 1) * freeCount p.2 m := Nat.mul_le_mul (Nat.mul_div_le _ _) (ih p.2).1
  · set E := n * (m / 2 * (n + 1) ^ (m - 2)) + (n + 1) ^ (m - 1) with hE
    have hterm : ∀ p ∈ antidiagonal n, (p.1 - 1) * freeCount p.2 m ≤
        2 ^ (m / 2) * 2 * ((p.1 - 1) / 2 * arndtCompositionCount (fun _ => True) p.2 m) + E := by
      rintro ⟨s, t⟩ hp
      rw [mem_antidiagonal] at hp
      dsimp only
      set q := (s - 1) / 2 with hq
      set a := arndtCompositionCount (fun _ => True) t m
      have hq1 : s - 1 ≤ 2 * q + 1 := by omega
      have hq2 : 2 * q ≤ n := by omega
      have hg := ih t
      have hgle : freeCount t m ≤ (n + 1) ^ (m - 1) := freeCount_le (by omega)
      have hpow : (t + 1) ^ (m - 2) ≤ (n + 1) ^ (m - 2) := Nat.pow_le_pow_left (by omega) _
      calc (s - 1) * freeCount t m ≤ (2 * q + 1) * freeCount t m := Nat.mul_le_mul_right _ hq1
        _ = 2 * q * freeCount t m + freeCount t m := by ring
        _ ≤ 2 * q * (2 ^ (m / 2) * a + m / 2 * (t + 1) ^ (m - 2)) + (n + 1) ^ (m - 1) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ hg.2) hgle
        _ = 2 ^ (m / 2) * 2 * (q * a) + (2 * q * (m / 2 * (t + 1) ^ (m - 2)) +
            (n + 1) ^ (m - 1)) := by ring
        _ ≤ 2 ^ (m / 2) * 2 * (q * a) + E := by
          rw [hE]
          gcongr
    calc ∑ p ∈ antidiagonal n, (p.1 - 1) * freeCount p.2 m
        ≤ ∑ p ∈ antidiagonal n,
            (2 ^ (m / 2) * 2 * ((p.1 - 1) / 2 * arndtCompositionCount (fun _ => True) p.2 m) +
              E) := sum_le_sum hterm
      _ = ∑ p ∈ antidiagonal n,
            2 ^ (m / 2) * 2 * ((p.1 - 1) / 2 * arndtCompositionCount (fun _ => True) p.2 m) +
              (n + 1) * E := by
          rw [sum_add_distrib, sum_const, Nat.card_antidiagonal, smul_eq_mul]
      _ ≤ _ := by
          apply Nat.add_le_add_left
          rw [hE, Nat.add_sub_cancel]
          rcases Nat.lt_or_ge m 2 with h2 | h2
          · obtain rfl : m = 1 := by omega
            simp
          · obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
            rw [Nat.add_sub_cancel, show j + 2 - 1 = j + 1 by omega]
            calc (n + 1) * (n * ((j + 2) / 2 * (n + 1) ^ j) + (n + 1) ^ (j + 1))
                = n * (n + 1) * ((j + 2) / 2 * (n + 1) ^ j) + (n + 1) ^ (j + 2) := by ring
              _ ≤ (n + 1) * (n + 1) * ((j + 2) / 2 * (n + 1) ^ j) + (n + 1) ^ (j + 2) := by
                gcongr
                exact Nat.le_succ n
              _ = ((j + 2) / 2 + 1) * (n + 1) ^ (j + 2) := by ring

private lemma bounds_all {m : ℕ} (hm : 1 ≤ m) : Bounds m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m, hm with
    | 1, _ => exact bounds_one
    | 2, _ => exact bounds_two
    | k + 3, _ => exact bounds_step (by omega) (ih (k + 1) (by omega) (by omega))

open Filter Asymptotics

private lemma freeCount_isEquivalent (m : ℕ) :
    (fun n : ℕ => (freeCount n m : ℝ)) ~[atTop]
      (fun n : ℕ => (n : ℝ) ^ (m - 1) / ((m - 1).factorial : ℝ)) := by
  have h1 : (fun n : ℕ => ((n - 1 : ℕ) : ℝ)) ~[atTop] (fun n : ℕ => (n : ℝ)) := by
    have hz : ∀ᶠ n : ℕ in atTop, (n : ℝ) ≠ 0 :=
      eventually_atTop.mpr ⟨1, fun n hn => by positivity⟩
    rw [isEquivalent_iff_tendsto_one hz, ← tendsto_add_atTop_iff_nat 1]
    simpa using tendsto_natCast_div_add_atTop (1 : ℝ)
  have h2 := (isEquivalent_choose (m - 1)).comp_tendsto (tendsto_sub_atTop_nat 1)
  have h3 := (h1.pow (m - 1)).div (IsEquivalent.refl (u := fun _ : ℕ => ((m - 1).factorial : ℝ)))
  refine (h2.trans h3).congr_left ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp [freeCount, show n ≠ 0 by omega]

private lemma error_isLittleO {m : ℕ} (hm : 1 ≤ m) :
    (fun n : ℕ => (2 ^ (m / 2) * arndtCompositionCount (fun _ => True) n m : ℝ) -
        freeCount n m) =o[atTop] (fun n : ℕ => (n : ℝ) ^ (m - 1) / ((m - 1).factorial : ℝ)) := by
  have hB := bounds_all hm
  rcases Nat.lt_or_ge m 2 with h2 | h2
  · obtain rfl : m = 1 := by omega
    have hz : (fun n : ℕ => (2 ^ (1 / 2) * arndtCompositionCount (fun _ => True) n 1 : ℝ) -
        freeCount n 1) = 0 := by
      funext n
      obtain ⟨h1, h2⟩ := hB n
      have : arndtCompositionCount (fun _ => True) n 1 = freeCount n 1 := by
        simp only [Nat.reduceDiv, pow_zero, one_mul, zero_mul, add_zero] at h1 h2
        omega
      simp [this]
    rw [hz]
    exact isLittleO_zero _ _
  · have hbig : (fun n : ℕ => (2 ^ (m / 2) * arndtCompositionCount (fun _ => True) n m : ℝ) -
        freeCount n m) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (m - 2)) := by
      apply IsBigO.of_bound ((m / 2 : ℕ) * 2 ^ (m - 2) : ℝ)
      filter_upwards [eventually_ge_atTop 1] with n hn
      obtain ⟨h1, h2⟩ := hB n
      have h1' : (2 : ℝ) ^ (m / 2) * arndtCompositionCount (fun _ => True) n m ≤ freeCount n m := by
        exact_mod_cast h1
      have h2' : (freeCount n m : ℝ) ≤ 2 ^ (m / 2) * arndtCompositionCount (fun _ => True) n m +
          (m / 2 : ℕ) * ((n : ℝ) + 1) ^ (m - 2) := by
        exact_mod_cast h2
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have h3 : ((n : ℝ) + 1) ^ (m - 2) ≤ 2 ^ (m - 2) * (n : ℝ) ^ (m - 2) := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (by linarith) _
      have hp : (0 : ℝ) ≤ (n : ℝ) ^ (m - 2) := by positivity
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp, abs_sub_comm,
        abs_of_nonneg (by linarith)]
      have hm2 : (0 : ℝ) ≤ (m / 2 : ℕ) := Nat.cast_nonneg _
      nlinarith
    have hsmall : (fun n : ℕ => (n : ℝ) ^ (m - 2)) =o[atTop]
        (fun n : ℕ => (n : ℝ) ^ (m - 1) / ((m - 1).factorial : ℝ)) := by
      have h := (isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) (show m - 2 < m - 1 by omega)).comp_tendsto
        tendsto_natCast_atTop_atTop
      refine h.trans_isBigO ?_
      apply IsBigO.of_bound ((m - 1).factorial : ℝ)
      filter_upwards with n
      have hf : (0 : ℝ) < (m - 1).factorial := by exact_mod_cast Nat.factorial_pos _
      simp only [Function.comp_apply, norm_div, norm_pow, Real.norm_natCast]
      rw [mul_div_cancel₀ _ hf.ne']
    exact hbig.trans_isLittleO hsmall

end arndtCompositionCount_isEquivalent

open Filter Asymptotics
open arndtCompositionCount_isEquivalent

/-- **Asymptotics of Arndt compositions with a fixed number of parts.** Let $a(n, m)$ be the
number of Arndt compositions of $n$ with $m$ parts. For every fixed integer $m \ge 1$,
$$a(n, m) \sim \frac{n^{m-1}}{2^{\lfloor m/2 \rfloor} (m-1)!} \quad (n \to \infty).$$

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Corollary 1 (`integers-2024-A35-cor-1`). -/
theorem arndtCompositionCount_isEquivalent (m : ℕ) (hm : 0 < m) :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n : ℕ => (arndtCompositionCount (fun _ => True) n m : ℝ))
      (fun n : ℕ => (n : ℝ) ^ (m - 1) / (2 ^ (m / 2) * (Nat.factorial (m - 1) : ℝ))) := by
  have hC := (freeCount_isEquivalent m).add_isLittleO (error_isLittleO hm)
  have hD := hC.div (IsEquivalent.refl (u := fun _ : ℕ => (2 : ℝ) ^ (m / 2)))
  have h2 : (2 : ℝ) ^ (m / 2) ≠ 0 := pow_ne_zero _ two_ne_zero
  refine (hD.congr_left (Eventually.of_forall fun n => ?_)).congr_right
    (Eventually.of_forall fun n => ?_)
  · simp only [Pi.add_apply, Pi.div_apply, add_sub_cancel]
    field_simp
  · simp only [Pi.div_apply]
    rw [div_div, mul_comm]

end

end MetaMathlibExt
