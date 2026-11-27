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
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.Monotone.Union
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Campbell's interpolation for the Szüsz–Volkmann counterexample

At positive integers the floor of Campbell's interpolation recovers the sequence whose decimal
blocks form his counterexample. On each block of integers from a power of ten to one less than
the next power, the defining sum for the sequence has constant increments.

Campbell's interpolation is monotone on $[0, \infty)$. On the last unit interval before each power
of ten it is an integral of a piecewise linear function, which is nonnegative because the
sequence jumps at that power of ten by at least the previous power of ten.
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

namespace campbellF_monotoneOn

private theorem ten_le_pow {k : ℕ} (hk : 1 ≤ k) : 10 ≤ 10 ^ k := by
  calc 10 = 10 ^ 1 := by norm_num
    _ ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hk

-- Every term of the defining sum over one decimal block is the same power of ten.
private theorem sum_block {k n : ℕ} (hk : 10 ≤ 10 ^ k) (hhi : n < 10 ^ (k + 1)) :
    ∑ i ∈ Finset.Icc (10 ^ k + 1) n, campbellH1 i = (n - 10 ^ k) * 10 ^ k := by
  rw [Finset.sum_const_nat (m := 10 ^ k) (by
    intro i hi
    obtain ⟨hli, hui⟩ := Finset.mem_Icc.mp hi
    have hilog := Nat.log_eq_of_pow_le_of_lt_pow (by omega : 10 ^ k ≤ i) (hui.trans_lt hhi)
    simp [campbellH1, hilog, show ¬ i < 10 by omega])]
  simp

-- The jump of `h₂` at `10 ^ (k + 1)` is at least `p = 10 ^ k`. The number
-- `h₂ (10 ^ (k + 1) - 1) + p` is a multiple `p * a` of `p`, and the sum defining
-- `h₂ (10 ^ (k + 1))` is at least `p * (a + 9)`; rounding it down to a multiple of `10 * p`
-- leaves at least `p * a`.
private theorem pow_add_campbellH2_le {k : ℕ} (hk : 1 ≤ k) :
    10 ^ k + campbellH2 (10 ^ (k + 1) - 1) ≤ campbellH2 (10 ^ (k + 1)) := by
  have hk10 := ten_le_pow hk
  have hP : 10 ^ (k + 1) = 10 * 10 ^ k := by ring
  have hlogP : Nat.log 10 (10 ^ (k + 1)) = k + 1 := Nat.log_pow (by norm_num) _
  have hlogP1 : Nat.log 10 (10 ^ (k + 1) - 1) = k :=
    Nat.log_eq_of_pow_le_of_lt_pow (by omega) (by omega)
  have hQ := sum_block hk10 (n := 10 ^ (k + 1) - 1) (by omega)
  have hh1 : campbellH1 (10 ^ (k + 1)) = 10 ^ (k + 1) := by
    simp [campbellH1, hlogP, show ¬ 10 ^ (k + 1) < 10 by omega]
  have hS : ∑ i ∈ Finset.Icc 1 (10 ^ (k + 1)), campbellH1 i =
      ∑ i ∈ Finset.Icc 1 (10 ^ k), campbellH1 i +
        ∑ i ∈ Finset.Icc (10 ^ k + 1) (10 ^ (k + 1) - 1), campbellH1 i +
          campbellH1 (10 ^ (k + 1)) := by
    have e1 : ∀ n, Finset.Icc 1 n = Finset.Ioc 0 n := fun n => Finset.Icc_add_one_left_eq_Ioc 0 n
    have e2 : ∀ n, Finset.Icc (10 ^ k + 1) n = Finset.Ioc (10 ^ k) n :=
      fun n => Finset.Icc_add_one_left_eq_Ioc _ n
    have h1 : 10 ^ (k + 1) = (10 ^ (k + 1) - 1) + 1 := by omega
    rw [e1, e1, e2]
    conv_lhs => rw [h1]
    rw [Finset.sum_Ioc_succ_top (by omega), ← h1,
      ← Finset.sum_Ioc_consecutive campbellH1 (Nat.zero_le (10 ^ k))
        (by omega : 10 ^ k ≤ 10 ^ (k + 1) - 1)]
  obtain ⟨d, hd⟩ : ∃ d, 10 ^ (k + 1) - 1 - 10 ^ k = d ∧ 9 * 10 ^ k = d + 1 :=
    ⟨10 ^ (k + 1) - 1 - 10 ^ k, rfl, by omega⟩
  have hempty : Finset.Icc (10 ^ (k + 1) + 1) (10 ^ (k + 1)) = ∅ := Finset.Icc_eq_empty (by omega)
  simp only [campbellH2, hlogP, hlogP1, hS, hQ, hh1, hempty, Finset.sum_empty, add_zero, hd.1]
  rw [hP]
  set p := 10 ^ k
  set s := ∑ i ∈ Finset.Icc 1 p, campbellH1 i
  have hp0 : 0 < p := by omega
  have hq : p * (s / p) ≤ s := Nat.mul_div_le s p
  have key1 : p * (s / p + d + 10) ≤ s + d * p + 10 * p := by nlinarith
  have key2 : (s / p + d + 10) / 10 ≤ (s + d * p + 10 * p) / (10 * p) := by
    rw [Nat.le_div_iff_mul_le (by positivity)]
    calc (s / p + d + 10) / 10 * (10 * p) = ((s / p + d + 10) / 10 * 10) * p := by ring
      _ ≤ (s / p + d + 10) * p := Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
      _ = p * (s / p + d + 10) := by ring
      _ ≤ _ := key1
  have key3 : s / p + d + 1 ≤ 10 * ((s / p + d + 10) / 10) := by omega
  calc p + (p * (s / p) + d * p) = p * (s / p + d + 1) := by ring
    _ ≤ p * (10 * ((s / p + d + 10) / 10)) := Nat.mul_le_mul_left _ key3
    _ = 10 * p * ((s / p + d + 10) / 10) := by ring
    _ ≤ 10 * p * ((s + d * p + 10 * p) / (10 * p)) := Nat.mul_le_mul_left _ key2

-- The jump `h₂(10^m) - h₂(10^m - 1)` that enters the definition of `h₃^{(m)}`.
private noncomputable def jump (m : ℕ) : ℝ :=
  (campbellH2 (10 ^ m) : ℝ) - campbellH2 (10 ^ m - 1)

private theorem pow_le_jump {k : ℕ} (hk : 1 ≤ k) : (10 : ℝ) ^ k ≤ jump (k + 1) := by
  have h : ((10 ^ k + campbellH2 (10 ^ (k + 1) - 1) : ℕ) : ℝ) ≤ campbellH2 (10 ^ (k + 1)) := by
    exact_mod_cast pow_add_campbellH2_le hk
  push_cast at h
  unfold jump
  linarith

-- `h₃^{(k+1)}` rewritten around the points `10^(k+1) - 1` and `10^(k+1)`, where it takes the
-- values `10^k` and `10^(k+1)`; both pieces equal `2 * jump - 19 * 10^k / 10` at the break point
-- `10^(k+1) - 1/10`.
private theorem campbellH3_eq (k : ℕ) (t : ℝ) :
    campbellH3 (k + 1) t =
      if t ≤ 10 * 10 ^ k - 1 / 10 then
        (20 * jump (k + 1) - 29 * 10 ^ k) / 9 * (t - (10 * 10 ^ k - 1)) + 10 ^ k
      else (119 * 10 ^ k - 20 * jump (k + 1)) * (t - 10 * 10 ^ k) + 10 * 10 ^ k := by
  have e1 : (10 : ℝ) ^ (k + 1) = 10 * 10 ^ k := by ring
  have e2 : (10 : ℝ) ^ (2 * (k + 1)) = 100 * (10 ^ k) ^ 2 := by ring
  have e3 : (10 : ℝ) ^ (2 * (k + 1) - 1) = 10 * (10 ^ k) ^ 2 := by
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
    ring
  simp only [campbellH3, jump, e1, e2, e3, Nat.add_sub_cancel]
  split_ifs <;> ring

private theorem continuous_campbellH3 (k : ℕ) : Continuous (campbellH3 (k + 1)) := by
  refine (Continuous.if_le (by fun_prop) (by fun_prop) continuous_id' continuous_const ?_).congr
    (fun t => (campbellH3_eq k t).symm)
  intro t ht
  rw [ht]
  ring

private theorem campbellH3_nonneg {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht₁ : 10 * 10 ^ k - 1 ≤ t)
    (ht₂ : t ≤ 10 * 10 ^ k) : 0 ≤ campbellH3 (k + 1) t := by
  have hH := pow_le_jump hk
  have hp : (0 : ℝ) < 10 ^ k := by positivity
  rw [campbellH3_eq]
  split_ifs with h
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 9 - 10 * (t - (10 * 10 ^ k - 1))) hp.le,
      mul_nonneg (by linarith : (0 : ℝ) ≤ t - (10 * 10 ^ k - 1))
        (by linarith : (0 : ℝ) ≤ 20 * jump (k + 1) - 19 * 10 ^ k)]
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 10 * (10 * 10 ^ k - t)) hp.le,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 10 * 10 ^ k - t)
        (by linarith : (0 : ℝ) ≤ 20 * jump (k + 1) - 19 * 10 ^ k)]

private theorem integral_affine (α β c u v : ℝ) :
    ∫ t in u..v, (α * (t - c) + β) = α * ((v - c) ^ 2 - (u - c) ^ 2) / 2 + β * (v - u) := by
  have hderiv : ∀ x ∈ Set.uIcc u v,
      HasDerivAt (fun t => α * (t - c) ^ 2 / 2 + β * t) (α * (x - c) + β) x := by
    intro x _
    have h := ((((hasDerivAt_id' x).sub_const c).fun_pow 2).const_mul α).div_const 2 |>.add
      ((hasDerivAt_id' x).const_mul β)
    convert h using 1
    simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous fun t : ℝ => α * (t - c) + β).intervalIntegrable u v)]
  ring

-- Over the last unit interval of a decimal block, `h₃` integrates to the jump of `h₂`.
private theorem integral_campbellH3 (k : ℕ) :
    ∫ t in (10 * 10 ^ k - 1 : ℝ)..(10 * 10 ^ k), campbellH3 (k + 1) t = jump (k + 1) := by
  have hc := continuous_campbellH3 k
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 10 * 10 ^ k - 1 / 10)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h₁ : ∫ t in (10 * 10 ^ k - 1 : ℝ)..(10 * 10 ^ k - 1 / 10), campbellH3 (k + 1) t =
      ∫ t in (10 * 10 ^ k - 1 : ℝ)..(10 * 10 ^ k - 1 / 10),
        ((20 * jump (k + 1) - 29 * 10 ^ k) / 9 * (t - (10 * 10 ^ k - 1)) + 10 ^ k) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by linarith)] at ht
    rw [campbellH3_eq, ite_eq_left ht.2]
  have h₂ : ∫ t in (10 * 10 ^ k - 1 / 10 : ℝ)..(10 * 10 ^ k), campbellH3 (k + 1) t =
      ∫ t in (10 * 10 ^ k - 1 / 10 : ℝ)..(10 * 10 ^ k),
        ((119 * 10 ^ k - 20 * jump (k + 1)) * (t - 10 * 10 ^ k) + 10 * 10 ^ k) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by linarith)] at ht
    rw [campbellH3_eq]
    split_ifs with h
    · rw [le_antisymm h ht.1]
      ring
    · rfl
  rw [h₁, h₂, integral_affine, integral_affine]
  ring

private theorem log_floor_eq {x : ℝ} {k : ℕ} (h₁ : (10 : ℝ) ^ k ≤ x) (h₂ : x < 10 ^ (k + 1)) :
    Nat.log 10 ⌊x⌋₊ = k := by
  have hx : 0 ≤ x := (by positivity : (0 : ℝ) ≤ 10 ^ k).trans h₁
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · exact Nat.le_floor (by exact_mod_cast h₁)
  · exact (Nat.floor_lt hx).2 (by exact_mod_cast h₂)

-- Campbell's interpolation beyond `10`, once the index of the decimal block is known.
private theorem campbellF_of_log {x : ℝ} {k : ℕ} (hx : 10 < x) (hk : Nat.log 10 ⌊x⌋₊ = k) :
    campbellF x =
      if x ≤ 10 ^ (k + 1) - 1 then
        (x * ((campbellH2 (10 ^ (k + 1) - 1) : ℝ) - campbellH2 (10 ^ k)) -
          (campbellH2 (10 ^ k) + 10 ^ k * (campbellH2 (10 ^ (k + 1) - 1) : ℝ) -
            10 ^ (k + 1) * campbellH2 (10 ^ k))) / (9 * 10 ^ k - 1)
      else
        (campbellH2 (10 ^ (k + 1) - 1) : ℝ) +
          ∫ t in ((10 : ℝ) ^ (k + 1) - 1)..x, campbellH3 (k + 1) t := by
  have h₁ : ¬ x ≤ 100 / 11 := by linarith
  have h₂ : ¬ x ≤ 10 := by linarith
  simp only [campbellF, h₁, h₂, hk, ite_false, Nat.add_sub_cancel]

-- On `[10^k, 10^(k+1) - 1]` Campbell's interpolation is affine with nonnegative slope.
private theorem monotoneOn_block {k : ℕ} (hk : 1 ≤ k) :
    MonotoneOn campbellF (Set.Icc ((10 : ℝ) ^ k) (10 ^ (k + 1) - 1)) := by
  have hk10 := ten_le_pow hk
  have hk10' : (10 : ℝ) ≤ 10 ^ k := by exact_mod_cast hk10
  have hD : (0 : ℝ) < 9 * 10 ^ k - 1 := by linarith
  have hy : (campbellH2 (10 ^ k) : ℝ) ≤ campbellH2 (10 ^ (k + 1) - 1) := by
    have hn : ((10 ^ k : ℕ) : ℝ) ≤ ((10 ^ (k + 1) - 1 : ℕ) : ℝ) := Nat.cast_le.2 (by omega)
    rw [Nat.cast_pow, Nat.cast_ofNat] at hn
    rw [floor_campbellF_eq_campbellH2.h2_on_block hk10 (n := 10 ^ (k + 1) - 1) (by omega)
      (by omega)]
    nlinarith
  refine MonotoneOn.congr (f₁ := fun x =>
    (x * ((campbellH2 (10 ^ (k + 1) - 1) : ℝ) - campbellH2 (10 ^ k)) -
      (campbellH2 (10 ^ k) + 10 ^ k * (campbellH2 (10 ^ (k + 1) - 1) : ℝ) -
        10 ^ (k + 1) * campbellH2 (10 ^ k))) / (9 * 10 ^ k - 1)) ?_ ?_
  · intro a _ b _ hab
    dsimp only
    gcongr
  · intro x hx
    rcases hx.1.eq_or_lt with h | h
    · have hf := floor_campbellF_eq_campbellH2.2 (10 ^ k) hk10
      push_cast at hf
      rw [← h, hf, div_eq_iff hD.ne']
      ring
    · rw [campbellF_of_log (by linarith) (log_floor_eq h.le (by linarith [hx.2])),
        ite_eq_left hx.2]

-- On `[10^(k+1) - 1, 10^(k+1)]` Campbell's interpolation is the integral of a nonnegative
-- function, and it reaches `h₂(10^(k+1))` at the right endpoint.
private theorem monotoneOn_tail {k : ℕ} (hk : 1 ≤ k) :
    MonotoneOn campbellF (Set.Icc ((10 : ℝ) ^ (k + 1) - 1) (10 ^ (k + 1))) := by
  have hk10 := ten_le_pow hk
  have hk10' : (10 : ℝ) ≤ 10 ^ k := by exact_mod_cast hk10
  have hP : (10 : ℝ) ^ (k + 1) = 10 * 10 ^ k := by ring
  have hc := continuous_campbellH3 k
  refine MonotoneOn.congr (f₁ := fun x => (campbellH2 (10 ^ (k + 1) - 1) : ℝ) +
    ∫ t in ((10 : ℝ) ^ (k + 1) - 1)..x, campbellH3 (k + 1) t) ?_ ?_
  · intro x hx y hy hxy
    dsimp only
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (a := (10 : ℝ) ^ (k + 1) - 1)
      (b := x) (c := y) (μ := MeasureTheory.volume) (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)
    have : 0 ≤ ∫ t in x..y, campbellH3 (k + 1) t :=
      intervalIntegral.integral_nonneg hxy fun t ht =>
        campbellH3_nonneg hk (by linarith [hx.1, ht.1]) (by linarith [hy.2, ht.2])
    linarith
  · intro x hx
    dsimp only
    rcases hx.1.eq_or_lt with h | h
    · have hcast : ((10 ^ (k + 1) - 1 : ℕ) : ℝ) = (10 : ℝ) ^ (k + 1) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num)), Nat.cast_pow, Nat.cast_ofNat,
          Nat.cast_one]
      rw [← h, intervalIntegral.integral_same, add_zero, ← hcast,
        floor_campbellF_eq_campbellH2.2 _ (by omega)]
    rcases hx.2.eq_or_lt with h' | h'
    · rw [h', hP, integral_campbellH3 k, jump, ← hP,
        show ((10 : ℝ) ^ (k + 1)) = ((10 ^ (k + 1) : ℕ) : ℝ) by push_cast; ring,
        floor_campbellF_eq_campbellH2.2 _ (by omega)]
      ring
    · rw [campbellF_of_log (by linarith) (log_floor_eq (by linarith) h'),
        ite_eq_right (not_le.2 h)]

private theorem monotoneOn_Icc_zero_ten : MonotoneOn campbellF (Set.Icc 0 10) := by
  have h₁ : MonotoneOn campbellF (Set.Icc 0 (100 / 11)) := by
    intro a ha b hb hab
    rw [campbellF, ite_eq_left ha.2, campbellF, ite_eq_left hb.2]
    gcongr
  have h₂ : MonotoneOn campbellF (Set.Icc (100 / 11) 10) := by
    refine MonotoneOn.congr (f₁ := fun x => 10 * x - 90) ?_ ?_
    · intro a _ b _ hab
      dsimp only
      linarith
    · intro x hx
      rcases hx.1.eq_or_lt with h | h
      · rw [← h, campbellF, ite_eq_left le_rfl]
        norm_num
      · rw [campbellF_of_mem h hx.2]
  rw [← Set.Icc_union_Icc_eq_Icc (b := 100 / 11) (by norm_num) (by norm_num)]
  exact h₁.union_right h₂ (isGreatest_Icc (by norm_num)) (isLeast_Icc (by norm_num))

private theorem monotoneOn_Icc_zero_pow (m : ℕ) :
    MonotoneOn campbellF (Set.Icc 0 (10 ^ (m + 1))) := by
  induction m with
  | zero => simpa using monotoneOn_Icc_zero_ten
  | succ k ih =>
    have hk : 1 ≤ k + 1 := by omega
    have hpos : (1 : ℝ) ≤ 10 ^ (k + 1) := one_le_pow₀ (by norm_num)
    have hle : (10 : ℝ) ^ (k + 1) ≤ 10 ^ (k + 1 + 1) - 1 := by
      rw [pow_succ _ (k + 1)]
      linarith
    have h₂₃ := (monotoneOn_block hk).union_right (monotoneOn_tail hk) (isGreatest_Icc hle)
      (isLeast_Icc (by linarith))
    rw [Set.Icc_union_Icc_eq_Icc hle (by linarith)] at h₂₃
    have h := ih.union_right h₂₃ (isGreatest_Icc (by positivity)) (isLeast_Icc (by linarith))
    rwa [Set.Icc_union_Icc_eq_Icc (by positivity) (by linarith)] at h

end campbellF_monotoneOn

/-- **Monotonicity of Campbell's interpolation.** Campbell's interpolation $f$ is monotone
(non-decreasing) on $[0, \infty)$: for all real numbers $x$ and $y$ with $0 \le x \le y$,
$f(x) \le f(y)$.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Lemma 5
(`jis-2026-26.3.4-lem-5`). -/
theorem campbellF_monotoneOn : MonotoneOn campbellF (Set.Ici 0) := by
  intro a ha b hb hab
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt b (by norm_num : (1 : ℝ) < 10)
  have hbn : b ≤ 10 ^ (n + 1) := hn.le.trans (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n))
  exact campbellF_monotoneOn.monotoneOn_Icc_zero_pow n ⟨ha, hab.trans hbn⟩ ⟨hb, hbn⟩ hab

end

end MetaMathlibExt
