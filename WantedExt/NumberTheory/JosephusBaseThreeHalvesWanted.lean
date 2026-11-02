/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Nth
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Rat.Defs
public import MathlibExt.Combinatorics.Enumerative.JosephusFunction
import Mathlib.Tactic

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
  | h N ih =>
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
  | h N ih =>
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

/-- **Base-3/2 digits of the next Josephus fixed point, gap zero.** Let $J_3$ be the Josephus
function with elimination step $3$, let $n_\ell$ be the $\ell$-th positive fixed point of $J_3$
in increasing order (counting from $\ell = 0$), and let $m_\ell$ be the number of integers $n$
with $n_\ell < n < n_{\ell+1}$ and $J_3(n) + 1 = n$ (the pure high extremal points between
them). For every $\ell$, if $m_\ell = 0$, then the base-$3/2$ digit list of $n_{\ell+1}$, least
significant digit first, is the digit $1$ followed by the digit list of $n_\ell$.

This is part (i) of the cited Theorem 1.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem_wanted josephusThreeFixedPoint_digits_of_gap_zero (ℓ : ℕ) :
    let D := baseThreeHalvesDigits (josephusThreeFixedPoint ℓ)
    let E := baseThreeHalvesDigits (josephusThreeFixedPoint (ℓ + 1))
    let m := josephusThreeGap ℓ
    m = 0 → E = 1 :: D

/-- **Base-3/2 digits of the next Josephus fixed point, gap one.** Let $J_3$ be the Josephus
function with elimination step $3$, let $n_\ell$ be the $\ell$-th positive fixed point of $J_3$
in increasing order (counting from $\ell = 0$), and let $m_\ell$ be the number of integers $n$
with $n_\ell < n < n_{\ell+1}$ and $J_3(n) + 1 = n$ (the pure high extremal points between
them). For every $\ell$, if $m_\ell = 1$, then the base-$3/2$ digit list of $n_{\ell+1}$, least
significant digit first, is the digits $2, 0$ followed by the digit list of $n_\ell$.

This is part (ii) of the cited Theorem 1.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem_wanted josephusThreeFixedPoint_digits_of_gap_one (ℓ : ℕ) :
    let D := baseThreeHalvesDigits (josephusThreeFixedPoint ℓ)
    let E := baseThreeHalvesDigits (josephusThreeFixedPoint (ℓ + 1))
    let m := josephusThreeGap ℓ
    m = 1 → E = [2, 0] ++ D

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
public theorem_wanted josephusThreeFixedPoint_digits_of_gap_at_least_two (ℓ : ℕ) :
    let D := baseThreeHalvesDigits (josephusThreeFixedPoint ℓ)
    let E := baseThreeHalvesDigits (josephusThreeFixedPoint (ℓ + 1))
    let m := josephusThreeGap ℓ
    2 ≤ m → E = 2 :: List.replicate (m - 1) 1 ++ 0 :: D

/-- **Digit count of consecutive Josephus fixed points.** Let $J_3$ be the Josephus function
with elimination step $3$, let $n_\ell$ be the $\ell$-th positive fixed point of $J_3$ in
increasing order (counting from $\ell = 0$), and let $m_\ell$ be the number of integers $n$ with
$n_\ell < n < n_{\ell+1}$ and $J_3(n) + 1 = n$ (the pure high extremal points between them).
For every $\ell$, the base-$3/2$ digit list of $n_{\ell+1}$ has exactly $m_\ell + 1$ more digits
than the base-$3/2$ digit list of $n_\ell$.

This is part (iv) of the cited Theorem 1.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem_wanted josephusThreeFixedPoint_digits_length (ℓ : ℕ) :
    let D := baseThreeHalvesDigits (josephusThreeFixedPoint ℓ)
    let E := baseThreeHalvesDigits (josephusThreeFixedPoint (ℓ + 1))
    let m := josephusThreeGap ℓ
    E.length = D.length + m + 1

end

end MetaMathlibExt
