/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Nth
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Rat.Defs
public import MathlibExt.Combinatorics.Enumerative.JosephusFunction
import MathlibExt.NumberTheory.JosephusFixedPointRecurrence
import MathlibExt.NumberTheory.JosephusHighExtremal
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Josephus fixed points in base 3/2

This module defines base-3/2 digits and proves that their length increases by one plus the number
of intervening pure high extremal points between consecutive step-three Josephus fixed points.
With one intervening pure high extremal point, the new digits are 2 and 0, least significant first.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Enumeration of the positive fixed points of $J_3$.** Let $J_3$ be the Josephus function
with step $3$. For $\ell \in \mathbb{N}$, $n_\ell$ is the $\ell$-th element, in increasing order
and counting from $\ell = 0$, of the set of natural numbers $n \ge 1$ with $J_3(n) = n$. Thus
$n_\ell$ is the paper's $n_p^{(\ell+1)}$.

If this set has at most $\ell$ elements, then $n_\ell = 0$ by convention.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public noncomputable def josephusThreeFixedPoint (ℓ : ℕ) : ℕ :=
  Nat.nth (fun n => 1 ≤ n ∧ josephus 3 n = n) ℓ

/-- **Gaps between consecutive positive fixed points of $J_3$.** Let $J_3$ be the Josephus
function with step $3$ and let $n_\ell$ be the $\ell$-th natural number $n \ge 1$ with
$J_3(n) = n$, in increasing order and counting from $\ell = 0$. For $\ell \in \mathbb{N}$, the gap
$g_\ell$ is the number of natural numbers $n$ with $n_\ell < n < n_{\ell+1}$ and
$J_3(n) + 1 = n$, that is, the number of pure high extremal points strictly between $n_\ell$ and
$n_{\ell+1}$. Thus $g_\ell$ is the paper's $\bar m_{\ell+1}$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public noncomputable def josephusThreeGap (ℓ : ℕ) : ℕ :=
  ((Finset.Ioo (josephusThreeFixedPoint ℓ) (josephusThreeFixedPoint (ℓ + 1))).filter
    (fun n => josephus 3 n + 1 = n)).card

/-- **Base-3/2 digits.** The base-$3/2$ digit list of a natural number $N$, least significant
digit first, is defined by recursion on $N$: the list of $0$ is empty, and for $N \ge 1$ it is
the digit $d = 2N \bmod 3$ followed by the base-$3/2$ digit list of $(2N - d)/3$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public def baseThreeHalvesDigits : ℕ → List ℕ
  | 0 => []
  | N + 1 =>
    let d := 2 * (N + 1) % 3
    d :: baseThreeHalvesDigits ((2 * (N + 1) - d) / 3)
  termination_by N => N
  decreasing_by omega

/-- The rational positional value of a little-endian digit list, before the paper's
factor of one half is applied.
Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
private def baseThreeHalvesValue (digits : List ℕ) : ℚ :=
  ∑ i : Fin digits.length, digits[i] * (3 / 2 : ℚ) ^ (i : ℕ)

/-- Prepending the least-significant digit contributes that digit and shifts every
old digit by one power of `3/2`.
Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
private theorem baseThreeHalvesValue_cons (d : ℕ) (digits : List ℕ) :
    baseThreeHalvesValue (d :: digits) =
      d + (3 / 2 : ℚ) * baseThreeHalvesValue digits := by
  unfold baseThreeHalvesValue
  simp only [List.length_cons]
  rw [Fin.sum_univ_succ]
  congr 1
  · simp
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change (digits.get i : ℚ) * (3 / 2 : ℚ) ^ (i + 1 : ℕ) =
      (3 / 2 : ℚ) * ((digits.get i : ℚ) * (3 / 2 : ℚ) ^ (i : ℕ))
    rw [pow_succ]
    ring

/-- **Base-3/2 digits of four.** The base-$3/2$ digit list of $4$, written least significant
digit first, is $(2, 1, 2)$; written most significant digit first, this is the paper's
$(212)_{3/2}$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem baseThreeHalvesDigits_four : baseThreeHalvesDigits 4 = [2, 1, 2] := by
  norm_num [baseThreeHalvesDigits]

/-- **Base-3/2 digits of thirteen.** The base-$3/2$ digit list of $13$, written least
significant digit first, is $(2, 1, 1, 0, 1, 2)$; written most significant digit first, this
is the paper's $(210112)_{3/2}$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem baseThreeHalvesDigits_thirteen :
    baseThreeHalvesDigits 13 = [2, 1, 1, 0, 1, 2] := by
  norm_num [baseThreeHalvesDigits]

/-- The positional value of the emitted little-endian digits is twice the encoded
natural number, accounting for the paper's factor of one half.
Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
private theorem baseThreeHalvesValue_digits (N : ℕ) :
    baseThreeHalvesValue (baseThreeHalvesDigits N) = 2 * (N : ℚ) := by
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    cases N with
    | zero => simp [baseThreeHalvesDigits, baseThreeHalvesValue]
    | succ n =>
      let d := 2 * (n + 1) % 3
      let q := (2 * (n + 1) - d) / 3
      have hq : q < n + 1 := by
        dsimp [q, d]
        omega
      have hn : 2 * (n + 1) = 3 * q + d := by
        dsimp [q, d]
        omega
      rw [baseThreeHalvesDigits]
      change baseThreeHalvesValue (d :: baseThreeHalvesDigits q) = _
      rw [baseThreeHalvesValue_cons, ih q hq]
      have hnq : (2 * (n + 1) : ℚ) = 3 * q + d := by
        exact_mod_cast hn
      norm_num [Nat.cast_add] at hnq ⊢
      linarith

/-- **Value of the base-3/2 digits.** For every natural number $N$, if
$(d_0, d_1, \dots, d_{k-1})$ is the base-$3/2$ digit list of $N$, least significant digit first,
then in $\mathbb{Q}$

$$2N = \sum_{i=0}^{k-1} d_i \left(\frac{3}{2}\right)^i.$$

Equivalently, the paper's expansion $\frac{1}{2} \sum_{i} d_i (3/2)^i$ has value $N$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem baseThreeHalvesDigits_value (N : ℕ) :
    2 * (N : ℚ) =
      ∑ i : Fin (baseThreeHalvesDigits N).length,
        (baseThreeHalvesDigits N)[i] * (3 / 2 : ℚ) ^ (i : ℕ) := by
  exact (baseThreeHalvesValue_digits N).symm

/-- **Base-3/2 digits are at most two.** For every natural number $N$, every digit $d$ in the
base-$3/2$ digit list of $N$ satisfies $d < 3$, that is, $d \in \{0, 1, 2\}$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem baseThreeHalvesDigits_lt_three (N d : ℕ)
    (hd : d ∈ baseThreeHalvesDigits N) : d < 3 := by
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    cases N with
    | zero => simp [baseThreeHalvesDigits] at hd
    | succ n =>
      let head := 2 * (n + 1) % 3
      let q := (2 * (n + 1) - head) / 3
      have hq : q < n + 1 := by
        dsimp [q, head]
        omega
      simp only [baseThreeHalvesDigits, List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact Nat.mod_lt _ (by omega)
      · exact ih q hq hd

/-- **The first positive fixed point of $J_3$ is $1$.** Let $J_3$ be the Josephus function with
step $3$ and let $n_\ell$ be the $\ell$-th natural number $n \ge 1$ with $J_3(n) = n$, in
increasing order and counting from $\ell = 0$. Then $n_0 = 1$; this is the paper's $n_p^{(1)}$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem josephusThreeFixedPoint_zero : josephusThreeFixedPoint 0 = 1 := by
  change Nat.nth (fun n => 1 ≤ n ∧ josephus 3 n = n) 0 = 1
  have hp : 1 ≤ 1 ∧ josephus 3 1 = 1 := by decide
  have hc : Nat.count (fun n => 1 ≤ n ∧ josephus 3 n = n) 1 = 0 := by decide
  rw [← hc]
  exact Nat.nth_count hp

/-- **Second positive fixed point of the Josephus function for step three.** Let $J_3$ be the
Josephus function with elimination step $3$. The second smallest positive integer $n$ with
$J_3(n) = n$ is $2$; in the zero-indexed enumeration $n_0 < n_1 < \cdots$ of these fixed points,
$n_1 = 2$, the paper's $n_p^{(2)}$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem josephusThreeFixedPoint_one : josephusThreeFixedPoint 1 = 2 := by
  change Nat.nth (fun n => 1 ≤ n ∧ josephus 3 n = n) 1 = 2
  have hp : 1 ≤ 2 ∧ josephus 3 2 = 2 := by decide
  have hc : Nat.count (fun n => 1 ≤ n ∧ josephus 3 n = n) 2 = 1 := by decide
  rw [← hc]
  exact Nat.nth_count hp

/-- **The third positive fixed point of $J_3$ is $13$.** Let $J_3$ be the Josephus function with
step $3$ and let $n_\ell$ be the $\ell$-th natural number $n \ge 1$ with $J_3(n) = n$, in
increasing order and counting from $\ell = 0$. Then $n_2 = 13$; this is the paper's $n_p^{(3)}$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem josephusThreeFixedPoint_two : josephusThreeFixedPoint 2 = 13 := by
  change Nat.nth (fun n => 1 ≤ n ∧ josephus 3 n = n) 2 = 13
  have hp : 1 ≤ 13 ∧ josephus 3 13 = 13 := by decide
  have hc : Nat.count (fun n => 1 ≤ n ∧ josephus 3 n = n) 13 = 2 := by decide
  rw [← hc]
  exact Nat.nth_count hp

/-- **The second gap between positive fixed points of $J_3$ is $3$.** Let $J_3$ be the Josephus
function with step $3$, let $n_\ell$ be the $\ell$-th natural number $n \ge 1$ with
$J_3(n) = n$ (in increasing order, counting from $\ell = 0$), and let $g_\ell$ be the number of
natural numbers $n$ with $n_\ell < n < n_{\ell+1}$ and $J_3(n) + 1 = n$. Then $g_1 = 3$; this is
the paper's $\bar m_2 = 3$.

Here $n_1 = 2$ and $n_2 = 13$, and the three pure high extremal points counted are $3$, $5$ and $8$.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem josephusThreeGap_one : josephusThreeGap 1 = 3 := by
  simp only [josephusThreeGap, josephusThreeFixedPoint_one,
    josephusThreeFixedPoint_two, Nat.reduceAdd]
  decide

namespace josephusThreeFixedPoint_digits_length

open MathlibExt.NumberTheory.JosephusWanted

private abbrev IsHigh (n : ℕ) : Prop :=
  1 ≤ n ∧ (josephus 3 n = n ∨ josephus 3 n + 1 = n)

private theorem exists_next_high {n : ℕ} (hn : IsHigh n) :
    ∃ m, n < m ∧ IsHigh m ∧ (∀ j, n < j → j < m → ¬ IsHigh j) ∧
      2 * m / 3 = n ∧
      (josephus 3 n + 1 = n → josephus 3 m + 1 = m → 2 * (m + 1) = 3 * (n + 1)) := by
  obtain ⟨hn, h⟩ := hn
  -- The deficit at a high extremal point is either zero or one.
  let d := n - josephus 3 n
  have hd : d ≤ 1 := by
    dsimp [d]
    omega
  have hj : josephus 3 n + d = n := by
    dsimp [d]
    omega
  have hreset : josephus 3 (n + 1) = 2 - d := by
    rw [josephus_succ 3 n (by decide) hn]
    have hmod : (josephus 3 n + 3 - 1) % (n + 1) = 1 - d := by
      have hsplit : josephus 3 n + 3 - 1 = 1 - d + (n + 1) := by omega
      rw [hsplit, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  -- After the reset, the deficit decreases by two until it is again at most one.
  let t := (n + d - 1) / 2
  let m := n + 1 + t
  have hlinear (i : ℕ) (hi : i ≤ t) :
      josephus 3 (n + 1 + i) = 2 - d + 3 * i := by
    by_cases hlarge : 3 ≤ n
    · have hhigh : IsHighExtremal 3 n := by
        change 1 ≤ josephus 3 (n + 1) ∧ josephus 3 (n + 1) ≤ 3 - 1
        omega
      have hbound : i ≤ (n - (josephus 3 (n + 1) - 1)) / (3 - 1) := by
        dsimp [t] at hi
        omega
      rw [josephus_add_eq_of_high 3 n i (by decide) hlarge hhigh hbound, hreset]
    · have hfixed : josephus 3 n = n := by
        obtain rfl | rfl : n = 1 ∨ n = 2 := by omega
        · decide
        · decide
      have hd_zero : d = 0 := by simp [d, hfixed]
      have hi_zero : i = 0 := by
        dsimp [t] at hi
        omega
      simpa [hi_zero] using hreset
  have hm := hlinear t le_rfl
  change josephus 3 m = 2 - d + 3 * t at hm
  have hgap : m - josephus 3 m = (n + d - 1) % 2 := by
    dsimp [m, t] at hm ⊢
    omega
  have hlt : n < m := by dsimp [m]; omega
  refine ⟨m, hlt, ⟨by omega, ?_⟩, ?_, ?_, ?_⟩
  · dsimp [m, t] at hm ⊢
    omega
  · intro j hnj hjm hjhigh
    obtain ⟨_, hjhigh⟩ := hjhigh
    have hindex : j = n + 1 + (j - (n + 1)) := by omega
    have hvalue := hlinear (j - (n + 1)) (by dsimp [m] at hjm; omega)
    rw [← hindex] at hvalue
    dsimp [m, t] at hjm
    omega
  · dsimp [m, t]
    omega
  · intro hpure hpure'
    have : d = 1 := by dsimp [d]; omega
    dsimp [m, t] at hgap ⊢
    omega

private theorem fixed_exists_ge {n : ℕ} (hn : IsHigh n) :
    ∃ m, n ≤ m ∧ 1 ≤ m ∧ josephus 3 m = m := by
  by_contra! hnone
  -- An infinite run of pure points would make the starting value plus one divisible
  -- by every power of two.
  have hdvd (k : ℕ) (a : ℕ) (ha : n ≤ a) (hah : IsHigh a) : 2 ^ k ∣ a + 1 := by
    induction k generalizing a with
    | zero => simp
    | succ k ih =>
      obtain ⟨b, hab, hbh, _, _, hpure⟩ := exists_next_high hah
      have hxa := hnone a ha hah.1
      have hxb := hnone b (by omega) hbh.1
      have heq := hpure (hah.2.resolve_left hxa) (hbh.2.resolve_left hxb)
      have hmul := Nat.mul_dvd_mul_left 2 (ih b (by omega) hbh)
      rw [← Nat.pow_succ', heq] at hmul
      exact ((by decide : Nat.Coprime 2 3).pow_left (k + 1)).dvd_of_dvd_mul_left hmul
  exact (n + 1).lt_two_pow_self.not_ge (Nat.le_of_dvd (by omega) (hdvd (n + 1) n le_rfl hn))

private theorem fixed_infinite : (Set.ofPred (fun n => 1 ≤ n ∧ josephus 3 n = n)).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro n
  have hhigh (n : ℕ) : ∃ m, n < m ∧ IsHigh m := by
    induction n with
    | zero => exact ⟨1, by decide, by decide⟩
    | succ n ih =>
      obtain ⟨a, hna, ha⟩ := ih
      obtain ⟨b, hab, hb, _⟩ := exists_next_high ha
      exact ⟨b, by omega, hb⟩
  obtain ⟨a, hna, ha⟩ := hhigh n
  obtain ⟨m, ham, hm, hfixed⟩ := fixed_exists_ge ha
  exact ⟨m, ⟨hm, hfixed⟩, by omega⟩

private theorem digits_length_step {n m : ℕ} (hm : 0 < m) (hprev : 2 * m / 3 = n) :
    (baseThreeHalvesDigits m).length = (baseThreeHalvesDigits n).length + 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  change 2 * (k + 1) / 3 = n at hprev
  have hquotient : (2 * (k + 1) - 2 * (k + 1) % 3) / 3 = n := by omega
  rw [baseThreeHalvesDigits, List.length_cons, hquotient]

private theorem digits_length_eq_add_card (distance n m : ℕ) (hn : IsHigh n) (hm : IsHigh m)
    (hle : n ≤ m) (hdistance : m - n = distance) :
    (baseThreeHalvesDigits m).length = (baseThreeHalvesDigits n).length +
      ((Finset.Ioc n m).filter IsHigh).card := by
  classical
  induction distance using Nat.strong_induction_on generalizing n m with
  | ind distance ih =>
    by_cases hnm : n = m
    · subst m
      simp
    obtain ⟨p, hnp, hp, hbetween, hquotient, _⟩ := exists_next_high hn
    have hpm : p ≤ m := by
      by_contra! hmp
      exact hbetween m (by omega) hmp hm
    have hsplit : (Finset.Ioc n m).filter IsHigh = insert p ((Finset.Ioc p m).filter IsHigh) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_insert]
      constructor
      · rintro ⟨⟨hnj, hjm⟩, hj⟩
        by_cases h : j = p
        · exact Or.inl h
        · exact Or.inr ⟨⟨by
            by_contra! h'
            exact hbetween j hnj (by omega) hj, hjm⟩, hj⟩
      · rintro (rfl | ⟨⟨hpj, hjm⟩, hj⟩)
        · exact ⟨⟨hnp, hpm⟩, hp⟩
        · exact ⟨⟨hnp.trans hpj, hjm⟩, hj⟩
    have hnot : p ∉ (Finset.Ioc p m).filter IsHigh := by simp
    rw [hsplit, Finset.card_insert_of_notMem hnot,
      ih (m - p) (by omega) p m hp hm hpm rfl, digits_length_step hp.1 hquotient]
    omega

end josephusThreeFixedPoint_digits_length

open josephusThreeFixedPoint_digits_length in
/-- **Digit count of consecutive Josephus fixed points.** Let $J_3$ be the Josephus function
with elimination step $3$, let $n_\ell$ be the $\ell$-th positive fixed point of $J_3$ in
increasing order (counting from $\ell = 0$), and let $m_\ell$ be the number of integers $n$ with
$n_\ell < n < n_{\ell+1}$ and $J_3(n) + 1 = n$ (the pure high extremal points between them).
For every $\ell$, the base-$3/2$ digit list of $n_{\ell+1}$ has exactly $m_\ell + 1$ more digits
than the base-$3/2$ digit list of $n_\ell$.

This is part (iv) of the cited Theorem 1.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem josephusThreeFixedPoint_digits_length (ℓ : ℕ) :
    let D := baseThreeHalvesDigits (josephusThreeFixedPoint ℓ)
    let E := baseThreeHalvesDigits (josephusThreeFixedPoint (ℓ + 1))
    let m := josephusThreeGap ℓ
    E.length = D.length + m + 1 := by
  dsimp only
  let n := josephusThreeFixedPoint ℓ
  let m := josephusThreeFixedPoint (ℓ + 1)
  change (baseThreeHalvesDigits m).length =
    (baseThreeHalvesDigits n).length + josephusThreeGap ℓ + 1
  have hinfinite := fixed_infinite
  have hn : 1 ≤ n ∧ josephus 3 n = n := Nat.nth_mem_of_infinite hinfinite ℓ
  have hm : 1 ≤ m ∧ josephus 3 m = m := Nat.nth_mem_of_infinite hinfinite (ℓ + 1)
  have hnm : n < m := Nat.nth_strictMono hinfinite (Nat.lt_succ_self ℓ)
  have hnoFixed {j : ℕ} (hnj : n < j) (hjm : j < m) : josephus 3 j ≠ j := by
    intro hj
    have := (Nat.nth_add_one_le_iff hinfinite (n := ℓ) ⟨by omega, hj⟩).mpr hnj
    exact (not_le_of_gt hjm) this
  classical
  have hsplit : (Finset.Ioc n m).filter IsHigh =
      insert m ((Finset.Ioo n m).filter (fun j => josephus 3 j + 1 = j)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ioo, Finset.mem_insert]
    constructor
    · rintro ⟨⟨hnj, hjm⟩, _, hj⟩
      rcases hjm.eq_or_lt with rfl | hjm
      · exact Or.inl rfl
      · exact Or.inr ⟨⟨hnj, hjm⟩, hj.resolve_left (hnoFixed hnj hjm)⟩
    · rintro (rfl | ⟨⟨hnj, hjm⟩, hj⟩)
      · exact ⟨⟨hnm, le_rfl⟩, hm.1, Or.inl hm.2⟩
      · exact ⟨⟨hnj, hjm.le⟩, by omega, Or.inr hj⟩
  have hnot : m ∉ (Finset.Ioo n m).filter (fun j => josephus 3 j + 1 = j) := by simp
  rw [digits_length_eq_add_card (m - n) n m ⟨hn.1, Or.inl hn.2⟩
    ⟨hm.1, Or.inl hm.2⟩ hnm.le rfl, hsplit, Finset.card_insert_of_notMem hnot]
  exact (Nat.add_assoc _ _ _).symm

namespace josephusThreeFixedPoint_digits_of_gap_one

private theorem digits_step {n m d : ℕ} (hm : 0 < m) (hd : d < 3)
    (h : 2 * m = 3 * n + d) : baseThreeHalvesDigits m = d :: baseThreeHalvesDigits n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have hrem : 2 * (k + 1) % 3 = d := by omega
  have hquot : (2 * (k + 1) - d) / 3 = n := by omega
  rw [baseThreeHalvesDigits.eq_2, hrem, hquot]

end josephusThreeFixedPoint_digits_of_gap_one

open josephusThreeFixedPoint_digits_length josephusThreeFixedPoint_digits_of_gap_one in
/-- **Base-3/2 digits of the next Josephus fixed point, gap one.** Let $J_3$ be the Josephus
function with elimination step $3$, let $n_\ell$ be the $\ell$-th positive fixed point of $J_3$
in increasing order (counting from $\ell = 0$), and let $m_\ell$ be the number of integers $n$
with $n_\ell < n < n_{\ell+1}$ and $J_3(n) + 1 = n$ (the pure high extremal points between
them). For every $\ell$, if $m_\ell = 1$, then the base-$3/2$ digit list of $n_{\ell+1}$, least
significant digit first, is the digits $2, 0$ followed by the digit list of $n_\ell$.

This is part (ii) of the cited Theorem 1.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem josephusThreeFixedPoint_digits_of_gap_one (ℓ : ℕ) :
    let D := baseThreeHalvesDigits (josephusThreeFixedPoint ℓ)
    let E := baseThreeHalvesDigits (josephusThreeFixedPoint (ℓ + 1))
    let m := josephusThreeGap ℓ
    m = 1 → E = [2, 0] ++ D := by
  dsimp only
  let a := josephusThreeFixedPoint ℓ
  let b := josephusThreeFixedPoint (ℓ + 1)
  change josephusThreeGap ℓ = 1 →
    baseThreeHalvesDigits b = [2, 0] ++ baseThreeHalvesDigits a
  intro hgap
  obtain ⟨hcount, hrec⟩ := josephusThree_fixedPoint_recurrence ℓ
  change josephusThreeGap ℓ = padicValNat 2 (3 * a + 2) at hcount
  change 2 ^ (padicValNat 2 (3 * a + 2) + 1) * b + 2 ^ padicValNat 2 (3 * a + 2) =
    3 ^ padicValNat 2 (3 * a + 2) * (3 * a + 2) at hrec
  rw [← hcount, hgap] at hrec
  norm_num at hrec
  -- The first digit is 2, and twice the resulting quotient is 3 times the old fixed point.
  let q := 2 * b / 3
  have hb : 2 * b = 3 * q + 2 := by dsimp [q]; omega
  have hq : 2 * q = 3 * a + 0 := by omega
  have ha : 1 ≤ a := (Nat.nth_mem_of_infinite fixed_infinite ℓ).1
  rw [digits_step (by omega) (by decide) hb, digits_step (by omega) (by decide) hq]
  rfl

namespace josephusThreeFixedPoint_digits_of_gap_at_least_two

open josephusThreeFixedPoint_digits_of_gap_one

-- A product of a power of two, a power of three and a positive number is positive.
private theorem chain_pos {u v t : ℕ} (ht : 1 ≤ t) : 1 ≤ 2 ^ u * 3 ^ v * t := by
  have ht0 : 0 < t := by omega
  have hpos : 0 < 2 ^ u * 3 ^ v * t :=
    mul_pos (mul_pos (pow_pos (by decide) u) (pow_pos (by decide) v)) ht0
  omega

-- The quotients `2 ^ u * 3 ^ v * t - 1` with `u + v + 1 = m` emit `v` digits `1` then `0`.
private theorem digits_of_chain {a m t : ℕ} (ht : 1 ≤ t)
    (hs : 3 * a + 2 = t * 2 ^ m) (ha : 1 ≤ a) :
    ∀ u v : ℕ, u + v + 1 = m →
      baseThreeHalvesDigits (2 ^ u * 3 ^ v * t - 1) =
        List.replicate v 1 ++ 0 :: baseThreeHalvesDigits a := by
  intro u v
  induction v generalizing u with
  | zero =>
    intro hm
    have hm' : u + 1 = m := by omega
    have h2X : 2 * (2 ^ u * 3 ^ 0 * t) = 3 * a + 2 := by
      calc (2 : ℕ) * (2 ^ u * 3 ^ 0 * t) = 2 ^ (u + 1) * t := by
            simp only [pow_zero, mul_one]
            ring
        _ = 2 ^ m * t := by rw [hm']
        _ = 3 * a + 2 := by rw [hs]; ring
    have hstep : 2 * (2 ^ u * 3 ^ 0 * t - 1) = 3 * a + 0 := by omega
    have hpos : 0 < 2 ^ u * 3 ^ 0 * t - 1 := by omega
    rw [digits_step hpos (by decide) hstep]
    simp only [List.replicate_zero, List.nil_append]
  | succ v ih =>
    intro hm
    have hY := ih (u + 1) (by omega)
    have h2XY : 2 * (2 ^ u * 3 ^ (v + 1) * t) = 3 * (2 ^ (u + 1) * 3 ^ v * t) := by
      ring
    have hX1 : 1 ≤ 2 ^ u * 3 ^ (v + 1) * t := chain_pos ht
    have hY1 : 1 ≤ 2 ^ (u + 1) * 3 ^ v * t := chain_pos ht
    have hstep : 2 * (2 ^ u * 3 ^ (v + 1) * t - 1) =
        3 * (2 ^ (u + 1) * 3 ^ v * t - 1) + 1 := by omega
    have hpos : 0 < 2 ^ u * 3 ^ (v + 1) * t - 1 := by omega
    rw [digits_step hpos (by decide) hstep, hY]
    simp only [List.replicate_succ, List.cons_append]

end josephusThreeFixedPoint_digits_of_gap_at_least_two

open josephusThreeFixedPoint_digits_length josephusThreeFixedPoint_digits_of_gap_one
  josephusThreeFixedPoint_digits_of_gap_at_least_two in
/-- **Base-3/2 digits of the next Josephus fixed point, gap at least two.** Let $J_3$ be the
Josephus function with elimination step $3$, let $n_\ell$ be the $\ell$-th positive fixed point
of $J_3$ in increasing order (counting from $\ell = 0$), and let $m_\ell$ be the number of
integers $n$ with $n_\ell < n < n_{\ell+1}$ and $J_3(n) + 1 = n$ (the pure high extremal points
between them). For every $\ell$, if $m_\ell \ge 2$, then the base-$3/2$ digit list of
$n_{\ell+1}$, least significant digit first, is the digit $2$, then $m_\ell - 1$ digits equal to
$1$, then the digit $0$, followed by the digit list of $n_\ell$.

Written most significant digit first, this appends to the digits of $n_\ell$ a $0$, then
$m_\ell - 1$ ones, then a $2$. This is part (iii) of the cited Theorem 1.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem josephusThreeFixedPoint_digits_of_gap_at_least_two (ℓ : ℕ) :
    let D := baseThreeHalvesDigits (josephusThreeFixedPoint ℓ)
    let E := baseThreeHalvesDigits (josephusThreeFixedPoint (ℓ + 1))
    let m := josephusThreeGap ℓ
    2 ≤ m → E = 2 :: List.replicate (m - 1) 1 ++ 0 :: D := by
  dsimp only
  let a := josephusThreeFixedPoint ℓ
  let b := josephusThreeFixedPoint (ℓ + 1)
  change 2 ≤ josephusThreeGap ℓ →
    baseThreeHalvesDigits b = 2 :: List.replicate (josephusThreeGap ℓ - 1) 1 ++
      0 :: baseThreeHalvesDigits a
  intro hgap
  obtain ⟨hcount, hrec⟩ := josephusThree_fixedPoint_recurrence ℓ
  change josephusThreeGap ℓ = padicValNat 2 (3 * a + 2) at hcount
  change 2 ^ (padicValNat 2 (3 * a + 2) + 1) * b + 2 ^ padicValNat 2 (3 * a + 2) =
    3 ^ padicValNat 2 (3 * a + 2) * (3 * a + 2) at hrec
  generalize hm : padicValNat 2 (3 * a + 2) = m at hcount hrec
  rw [hcount] at hgap ⊢
  have hs : 3 * a + 2 = Nat.divMaxPow (3 * a + 2) 2 * 2 ^ m := by
    rw [← hm, Nat.divMaxPow_mul_pow_padicValNat]
  generalize Nat.divMaxPow (3 * a + 2) 2 = t at hs
  have hb : 2 * b + 1 = t * 3 ^ m := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < 2) m)
    rw [hs] at hrec
    rw [Nat.mul_add, ← Nat.mul_assoc, ← pow_succ, Nat.mul_one, hrec]
    ring
  have ht : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · omega
    · exact hpos
  have hm1 : m = (m - 1) + 1 := by omega
  have ha1 : 1 ≤ a := (Nat.nth_mem_of_infinite fixed_infinite ℓ).1
  have hq1 : baseThreeHalvesDigits (2 ^ 0 * 3 ^ (m - 1) * t - 1) =
      List.replicate (m - 1) 1 ++ 0 :: baseThreeHalvesDigits a :=
    digits_of_chain ht hs ha1 0 (m - 1) (by omega)
  have hb1 : 1 ≤ b := (Nat.nth_mem_of_infinite fixed_infinite (ℓ + 1)).1
  have h3m : t * 3 ^ m = 3 * (2 ^ 0 * 3 ^ (m - 1) * t) := by
    conv_lhs => rw [hm1, pow_succ]
    ring
  have hstep : 2 * b = 3 * (2 ^ 0 * 3 ^ (m - 1) * t - 1) + 2 := by omega
  rw [digits_step (by omega) (by decide) hstep, hq1]
  simp only [List.cons_append]

end

end MetaMathlibExt
