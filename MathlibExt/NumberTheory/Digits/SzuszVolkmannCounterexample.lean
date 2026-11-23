/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Campbell's interpolation for the Szüsz–Volkmann counterexample

At positive integers the floor of Campbell's interpolation recovers the sequence whose decimal
blocks form his counterexample. On each block of integers from a power of ten to one less than
the next power, the defining sum for the sequence has constant increments.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Campbell's sequence $h_1$.** For a natural number $n$, $h_1(n) = 0$ if $n < 10$ and
$h_1(n) = 10^{\lfloor \log_{10} n \rfloor}$ if $n \ge 10$; thus for $n \ge 10$, $h_1(n)$ is the
largest power of $10$ that is at most $n$.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Section 2 (definition of `h₁`). -/
def campbellH1 (n : ℕ) : ℕ :=
  if n < 10 then 0 else 10 ^ Nat.log 10 n

/-- **Small values of $h_1$.** Campbell's auxiliary sequence $h_1$ satisfies $h_1(9) = 0$,
$h_1(10) = 10$, $h_1(99) = 10$ and $h_1(100) = 100$.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Section 2. -/
theorem campbellH1_small :
    campbellH1 9 = 0 ∧ campbellH1 10 = 10 ∧ campbellH1 99 = 10 ∧ campbellH1 100 = 100 := by
  decide

/-- **Campbell's sequence $h_2$.** For a natural number $n$, let $k = \lfloor \log_{10} n \rfloor$
(with $k = 0$ for $n = 0$), let $h_1$ be Campbell's sequence and let
$S_k = \sum_{i=1}^{10^k} h_1(i)$. Then
$h_2(n) = 10^k \lfloor S_k / 10^k \rfloor + \sum_{i=10^k+1}^{n} h_1(i)$, where the last sum is
empty when $n \le 10^k$.

This is OEIS A380904.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Section 2, Equation (6)
(definition of `h₂`). -/
def campbellH2 (n : ℕ) : ℕ :=
  10 ^ Nat.log 10 n * ((∑ i ∈ Finset.Icc 1 (10 ^ Nat.log 10 n), campbellH1 i) / 10 ^ Nat.log 10 n) +
    ∑ i ∈ Finset.Icc (10 ^ Nat.log 10 n + 1) n, campbellH1 i

/-- **Small values of Campbell's sequence $h_2$.** The sequence $h_2$ satisfies $h_2(9) = 0$,
$h_2(10) = 10$, $h_2(21) = 120$, $h_2(99) = 900$ and $h_2(100) = 1000$.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Example 1 and Section 2.1. -/
theorem campbellH2_small :
    campbellH2 9 = 0 ∧ campbellH2 10 = 10 ∧ campbellH2 21 = 120 ∧ campbellH2 99 = 900 ∧
      campbellH2 100 = 1000 := by
  decide +kernel

/-- **Campbell's auxiliary function $h_3^{(m)}$.** For a natural number $m$, let
$H(m) = h_2(10^m) - h_2(10^m - 1)$, where $h_2$ is Campbell's sequence (in the paper's notation
$H(m) = y_1(m + 1) - y_2(m)$ with $y_1(n) = h_2(10^{n-1})$ and $y_2(n) = h_2(10^n - 1)$). Define
$h_3^{(m)} : \mathbb{R} \to \mathbb{R}$ by $h_3^{(m)}(t) = a(m)\,t + b(m)$ for
$t \le 10^m - 1/10$ and $h_3^{(m)}(t) = c(m)\,t + d(m)$ for $t > 10^m - 1/10$, where
$a(m) = (20H(m) - 11 \cdot 10^m)/9 + 9 \cdot 10^{m-1}$,
$b(m) = (10^m - 1)(-20H(m) + 11 \cdot 10^m)/9 + 10^m - 9 \cdot 10^{2m-1}$,
$c(m) = -20H(m) + 9 \cdot 10^{m-1} + 11 \cdot 10^m$ and
$d(m) = 20 \cdot 10^m H(m) - 11 \cdot 10^{2m} - 9 \cdot 10^{2m-1} + 10^m$, with the exponents
$m - 1$ and $2m - 1$ read as $0$ when $m = 0$.

The paper uses $h_3^{(m)}$ only on $[10^m - 1, 10^m]$ for $m \ge 2$.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Section 2.2, Equations (16)-(20). -/
noncomputable def campbellH3 (m : ℕ) (t : ℝ) : ℝ :=
  let H : ℝ := (campbellH2 (10 ^ m) : ℝ) - campbellH2 (10 ^ m - 1)
  if t ≤ 10 ^ m - 1 / 10 then
    ((20 * H - 11 * 10 ^ m) / 9 + 9 * 10 ^ (m - 1)) * t +
      ((10 ^ m - 1) * (-20 * H + 11 * 10 ^ m) / 9 + 10 ^ m - 9 * 10 ^ (2 * m - 1))
  else
    (-20 * H + 9 * 10 ^ (m - 1) + 11 * 10 ^ m) * t +
      (20 * 10 ^ m * H - 11 * 10 ^ (2 * m) - 9 * 10 ^ (2 * m - 1) + 10 ^ m)

/-- **First piece of Campbell's auxiliary function $h_3^{(m)}$.** For every natural number $m$
and every real number $t \le 10^m - 1/10$, $h_3^{(m)}(t) = a(m)\,t + b(m)$, where
$H(m) = h_2(10^m) - h_2(10^m - 1)$ with $h_2$ Campbell's sequence,
$a(m) = (20H(m) - 11 \cdot 10^m)/9 + 9 \cdot 10^{m-1}$ and
$b(m) = (10^m - 1)(-20H(m) + 11 \cdot 10^m)/9 + 10^m - 9 \cdot 10^{2m-1}$, with the exponents
$m - 1$ and $2m - 1$ read as $0$ when $m = 0$.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Section 2.2. -/
theorem campbellH3_of_le {m : ℕ} {t : ℝ} (ht : t ≤ 10 ^ m - 1 / 10) :
    campbellH3 m t =
      ((20 * ((campbellH2 (10 ^ m) : ℝ) - campbellH2 (10 ^ m - 1)) - 11 * 10 ^ m) / 9 +
          9 * 10 ^ (m - 1)) * t +
        ((10 ^ m - 1) * (-20 * ((campbellH2 (10 ^ m) : ℝ) - campbellH2 (10 ^ m - 1)) +
            11 * 10 ^ m) / 9 + 10 ^ m - 9 * 10 ^ (2 * m - 1)) := by
  simp only [campbellH3, ht, ite_true]

/-- **Campbell's interpolation.** Let $h_2$ be Campbell's sequence and $h_3^{(m)}$ the auxiliary
piecewise-linear functions of the construction, and for $n \ge 1$ put $y_1(n) = h_2(10^{n-1})$ and
$y_2(n) = h_2(10^n - 1)$. Campbell's interpolation is the function $f : \mathbb{R} \to \mathbb{R}$
with $f(x) = \frac{89}{110} e^{(100/89)(11x - 100)} + \frac{1}{10}$ for $x \le 100/11$ and
$f(x) = 10x - 90$ for $100/11 < x \le 10$. For $x > 10$ put
$m = \lfloor \log_{10} \lfloor x \rfloor \rfloor + 1$, so that $m \ge 2$ and
$10^{m-1} \le x < 10^m$; then
$$
f(x) = \frac{x (y_2(m) - y_1(m)) - (y_1(m) + 10^{m-1} y_2(m) - 10^m y_1(m))}{9 \cdot 10^{m-1} - 1}
$$
if $x \le 10^m - 1$, and $f(x) = h_2(10^m - 1) + \int_{10^m - 1}^{x} h_3^{(m)}(t) \, dt$ if
$x > 10^m - 1$.

The paper defines $f$ on $[0, \infty)$ only; here the first formula is used for every
$x \le 100/11$. At a power of ten $x = 10^{m-1} > 10$ the formula for index $m$ is used; the piece
to its left takes the same value there.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Section 2.2, Equations (15) and (21). -/
noncomputable def campbellF (x : ℝ) : ℝ :=
  if x ≤ 100 / 11 then 89 / 110 * Real.exp (100 / 89 * (11 * x - 100)) + 1 / 10
  else if x ≤ 10 then 10 * x - 90
  else
    let m := Nat.log 10 ⌊x⌋₊ + 1
    let y₁ : ℝ := campbellH2 (10 ^ (m - 1))
    let y₂ : ℝ := campbellH2 (10 ^ m - 1)
    if x ≤ 10 ^ m - 1 then
      (x * (y₂ - y₁) - (y₁ + 10 ^ (m - 1) * y₂ - 10 ^ m * y₁)) / (9 * 10 ^ (m - 1) - 1)
    else
      y₂ + ∫ t in ((10 : ℝ) ^ m - 1)..x, campbellH3 m t

/-- **Campbell's interpolation on $(100/11, 10]$.** For every real $x$ with $100/11 < x \le 10$,
Campbell's interpolation satisfies $f(x) = 10x - 90$.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Section 2.2. -/
theorem campbellF_of_mem {x : ℝ} (h₁ : 100 / 11 < x) (h₂ : x ≤ 10) : campbellF x = 10 * x - 90 := by
  simp [campbellF, not_le.2 h₁, h₂]

/-- **Decimal digit block of $h_2(n)$.** For a natural number $n$, the block of $n$ is the list of
base-$10$ digits of $h_2(n)$, where $h_2$ is Campbell's sequence, written most significant digit
first; when $h_2(n) = 0$ the block is the single digit $0$.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Section 1.1 (the expansion
`0.b₁b₂…` with `b_n` the base-`g` expansion of `⌊f(n)⌋`). -/
def campbellBlock (n : ℕ) : List ℕ :=
  if campbellH2 n = 0 then [0] else (Nat.digits 10 (campbellH2 n)).reverse

/-- **Digits of the concatenation $0.h_2(1)h_2(2)\ldots$.** Let $h_2$ be Campbell's sequence.
For $j \ge 0$, $d_j$ is the digit in position $j$ (counting from $0$) after the decimal point of
$0.h_2(1)h_2(2)\ldots$, the string obtained by writing the blocks of $h_2(1), h_2(2), \ldots$ one
after another, where the block of $h_2(n)$ is its list of base-$10$ digits, most significant
first, with $0$ written as the single digit $0$.

Every block is nonempty, so $d_j$ already lies in the first $j + 1$ blocks.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Theorem 8 (the concatenation
`0.h₂(1)h₂(2)…`). -/
def campbellConcatDigit (j : ℕ) : ℕ :=
  ((List.range (j + 1)).flatMap fun i => campbellBlock (i + 1)).getD j 0

/-- **The first eleven digits of the concatenation $0.h_2(1)h_2(2)\ldots$.** Let $h_2$ be
Campbell's sequence and let $d_0, d_1, d_2, \ldots$ be the digits after the decimal point of
$0.h_2(1)h_2(2)\ldots$, the concatenation of the base-$10$ digit blocks of $h_2(1), h_2(2), \ldots$
(with $0$ written as the single digit $0$). Then
$(d_0, d_1, \ldots, d_{10}) = (0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0)$: nine zero blocks from
$h_2(1) = \cdots = h_2(9) = 0$, then the block of $h_2(10) = 10$.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Example 1. -/
theorem campbellConcatDigit_small :
    (List.range 11).map campbellConcatDigit = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0] := by
  decide +kernel

/-- **Campbell's constant.** Let $h_2$ be Campbell's sequence. Campbell's constant is the real
number $\sum_{j \ge 0} d_j \, 10^{-(j+1)} = 0.d_0 d_1 d_2 \ldots$, where $d_0, d_1, d_2, \ldots$
are the digits after the decimal point of the concatenation $0.h_2(1)h_2(2)\ldots$ of the
base-$10$ digit blocks of $h_2(1), h_2(2), \ldots$ (with $0$ written as the single digit $0$).

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Theorem 8. -/
noncomputable def campbellConstant : ℝ :=
  ∑' j : ℕ, (campbellConcatDigit j : ℝ) / 10 ^ (j + 1)

namespace floor_campbellF_eq_campbellH2

-- Within a single decimal block every term in the tail sum is the same power of ten.
private theorem h2_on_block {k n : ℕ} (hk : 10 ≤ 10 ^ k) (hlo : 10 ^ k ≤ n)
    (hhi : n < 10 ^ (k + 1)) :
    (campbellH2 n : ℝ) = campbellH2 (10 ^ k) + (n - (10 : ℝ) ^ k) * 10 ^ k := by
  have hlog := Nat.log_eq_of_pow_le_of_lt_pow hlo hhi
  have hsum : ∑ i ∈ Finset.Icc (10 ^ k + 1) n, campbellH1 i = (n - 10 ^ k) * 10 ^ k := by
    rw [Finset.sum_const_nat (m := 10 ^ k) (by
      intro i hi
      obtain ⟨hli, hui⟩ := Finset.mem_Icc.mp hi
      have hilog := Nat.log_eq_of_pow_le_of_lt_pow (by omega : 10 ^ k ≤ i) (hui.trans_lt hhi)
      simp [campbellH1, hilog, show ¬ i < 10 by omega])]
    simp
  have hnat : campbellH2 n = campbellH2 (10 ^ k) + (n - 10 ^ k) * 10 ^ k := by
    simp [campbellH2, hlog, Nat.log_pow (by decide : 1 < 10), hsum]
  rw [hnat, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hlo, Nat.cast_pow, Nat.cast_ofNat]

private theorem eq_of_ten_le (n : ℕ) (hn : 10 ≤ n) : campbellF n = campbellH2 n := by
  rcases hn.eq_or_lt with rfl | hn
  · rw [campbellF_of_mem (by norm_num) (by norm_num), campbellH2_small.2.1]
    norm_num
  set k := Nat.log 10 n with hklog
  have hlo : 10 ^ k ≤ n := Nat.pow_log_le_self 10 (by omega)
  have hhi : n < 10 ^ (k + 1) := Nat.lt_pow_succ_log_self (by decide) n
  have hk : 10 ≤ 10 ^ k := by
    have hk' : 1 ≤ k := Nat.le_log_of_pow_le (by decide) (by simpa using hn.le)
    exact (show 10 ^ 1 ≤ 10 ^ k from Nat.pow_le_pow_right (by decide) hk')
  have hlast : n ≤ 10 ^ (k + 1) - 1 := by omega
  have hpos : 1 ≤ 10 ^ (k + 1) := by omega
  have hn' : (n : ℝ) ≤ 10 ^ (k + 1) - 1 := by
    apply le_sub_iff_add_le.mpr
    exact_mod_cast hhi
  have hy := h2_on_block hk (hlo.trans hlast) (Nat.sub_lt hpos Nat.zero_lt_one)
  rw [Nat.cast_sub hpos, Nat.cast_pow, Nat.cast_ofNat] at hy
  have hten : (10 : ℝ) < n := by exact_mod_cast hn
  have hcut : ¬ (n : ℝ) ≤ 100 / 11 := by linarith
  simp only [campbellF, ite_eq_right hcut, ite_eq_right hten.not_ge, Nat.floor_natCast,
    ← hklog, Nat.add_sub_cancel, ite_eq_left hn']
  rw [hy, h2_on_block hk hlo hhi, pow_succ]
  have hp : (1 : ℝ) ≤ 10 ^ k := by exact_mod_cast (show 1 ≤ 10 ^ k by omega)
  apply (div_eq_iff (by linarith : (9 : ℝ) * 10 ^ k - 1 ≠ 0)).2
  ring

private theorem floor_eq (n : ℕ) (hn : 1 ≤ n) : ⌊campbellF n⌋₊ = campbellH2 n := by
  by_cases hten : 10 ≤ n
  · rw [eq_of_ten_le n hten, Nat.floor_natCast]
  have hsmall : campbellH2 n = 0 := by
    interval_cases n <;> decide
  rw [hsmall, Nat.floor_eq_zero]
  have hn' : (n : ℝ) ≤ 9 := by exact_mod_cast (show n ≤ 9 by omega)
  rw [campbellF, ite_eq_left (show (n : ℝ) ≤ 100 / 11 by linarith)]
  have hexp : Real.exp (100 / 89 * (11 * n - 100)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  linarith

end floor_campbellF_eq_campbellH2

/-- **The floor of Campbell's interpolation at positive integers is Campbell's sequence $h_2$.**
Let $f$ be Campbell's interpolation and $h_2$ Campbell's sequence. For every integer $n \ge 1$,
$\lfloor f(n) \rfloor = h_2(n)$, and for every integer $n \ge 10$, $f(n) = h_2(n)$.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Lemma 3
(`jis-2026-26.3.4-lem-3`). -/
theorem floor_campbellF_eq_campbellH2 :
    (∀ n : ℕ, 1 ≤ n → ⌊campbellF n⌋₊ = campbellH2 n) ∧
    ∀ n : ℕ, 10 ≤ n → campbellF n = campbellH2 n := by
  exact ⟨floor_campbellF_eq_campbellH2.floor_eq, floor_campbellF_eq_campbellH2.eq_of_ten_le⟩

end

end MetaMathlibExt
