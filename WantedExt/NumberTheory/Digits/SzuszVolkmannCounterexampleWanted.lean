/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A counterexample to Szüsz and Volkmann's construction of normal numbers

Statements from John M. Campbell, *A Counterexample to a Purported Construction of Normal
Numbers*, Journal of Integer Sequences 29 (2026), Article 26.3.4.

The paper builds an integer sequence `h₂` (OEIS A380904) whose terms grow quadratically but carry
many trailing zeros, and a differentiable increasing interpolation `f` with `⌊f(n)⌋ = h₂(n)`,
`η(f) = 2` and `η(f') = 1`, where `η(h) = lim_{x → ∞} log h(x) / log x`. Szüsz and Volkmann's
Theorem 2 would make `0.h₂(1)h₂(2)…` normal; the paper shows it is not. Normality uses
`MetaMathlibExt.NormalNumber.IsNormalInBase`.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import MathlibExt.NumberTheory.NormalNumber

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

/-- **Sums of $h_1$ and the jumps of $h_2$ at powers of ten.** Let $h_1$ be Campbell's auxiliary
sequence and $h_2$ Campbell's sequence. For every integer $\ell \ge 1$,
$\sum_{i=1}^{10^{\ell+1}-1} h_1(i) = \sum_{j=0}^{\ell-1} 900 \cdot 100^j$, the number written
$9090\cdots900$ ($\ell$ blocks $90$, then $0$). Moreover, writing $y_1(n) = h_2(10^{n-1})$ and
$y_2(n) = h_2(10^n - 1)$, for every integer $\ell \ge 2$ we have
$(y_2(\ell) - y_1(\ell)) / (9 \cdot 10^{\ell-1} - 1) = 10^{\ell-1}$ and
$y_1(\ell + 1) - y_2(\ell) = 10^{2\lfloor \ell/2 \rfloor}$.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Lemma 2
(`jis-2026-26.3.4-lem-2`). -/
public theorem_wanted campbellH1_sum_and_y_relations :
    (∀ ℓ : ℕ, 1 ≤ ℓ →
      ∑ i ∈ Finset.Icc 1 (10 ^ (ℓ + 1) - 1), campbellH1 i = ∑ j ∈ Finset.range ℓ, 900 * 100 ^ j) ∧
    ∀ ℓ : ℕ, 2 ≤ ℓ →
      ((campbellH2 (10 ^ ℓ - 1) : ℚ) - campbellH2 (10 ^ (ℓ - 1))) / (9 * 10 ^ (ℓ - 1) - 1) =
          10 ^ (ℓ - 1) ∧
        (campbellH2 (10 ^ ℓ) : ℤ) - campbellH2 (10 ^ ℓ - 1) = 10 ^ (2 * (ℓ / 2))

/-- **The floor of Campbell's interpolation at positive integers is Campbell's sequence $h_2$.**
Let $f$ be Campbell's interpolation and $h_2$ Campbell's sequence. For every integer $n \ge 1$,
$\lfloor f(n) \rfloor = h_2(n)$, and for every integer $n \ge 10$, $f(n) = h_2(n)$.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Lemma 3
(`jis-2026-26.3.4-lem-3`). -/
public theorem_wanted floor_campbellF_eq_campbellH2 :
    (∀ n : ℕ, 1 ≤ n → ⌊campbellF n⌋₊ = campbellH2 n) ∧
    ∀ n : ℕ, 10 ≤ n → campbellF n = campbellH2 n

/-- **Differentiability of Campbell's interpolation.** Campbell's interpolation $f$ is
differentiable at every real $x > 0$.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Lemma 4
(`jis-2026-26.3.4-lem-4`). -/
public theorem_wanted campbellF_differentiableOn : DifferentiableOn ℝ campbellF (Set.Ioi 0)

/-- **Monotonicity of Campbell's interpolation.** Campbell's interpolation $f$ is monotone
(non-decreasing) on $[0, \infty)$: for all real numbers $x$ and $y$ with $0 \le x \le y$,
$f(x) \le f(y)$.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Lemma 5
(`jis-2026-26.3.4-lem-5`). -/
public theorem_wanted campbellF_monotoneOn : MonotoneOn campbellF (Set.Ici 0)

/-- **Growth exponent of Campbell's interpolation.** For Campbell's interpolation $f$,
$\log f(x) / \log x \to 2$ as $x \to \infty$ over the reals; that is, $\eta(f) = 2$, where
$\eta(h) = \lim_{x \to \infty} \log h(x) / \log x$.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Lemma 6
(`jis-2026-26.3.4-lem-6`). -/
public theorem_wanted tendsto_log_campbellF_div_log :
    Filter.Tendsto (fun x => Real.log (campbellF x) / Real.log x) Filter.atTop (nhds 2)

/-- **Growth exponent of the derivative of Campbell's interpolation.** For Campbell's
interpolation $f$, $\log f'(x) / \log x \to 1$ as $x \to \infty$ over the reals; that is,
$\eta(f') = 1$, where $\eta(h) = \lim_{x \to \infty} \log h(x) / \log x$. Here $f'(x)$ is taken
to be $0$ at any point where $f$ is not differentiable, and $\log 0 = 0$.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Lemma 7
(`jis-2026-26.3.4-lem-7`). -/
public theorem_wanted tendsto_log_deriv_campbellF_div_log :
    Filter.Tendsto (fun x => Real.log (deriv campbellF x) / Real.log x) Filter.atTop (nhds 1)

/-- **Campbell's concatenation of $h_2$ is not normal in base $10$.** Let $h_2$ be Campbell's
sequence and let $c_0, c_1, c_2, \ldots$ be the base-$10$ digits of $h_2(1), h_2(2), \ldots$,
each number written most significant digit first and the numbers written one after another (with
$h_2(n) = 0$ written as the single digit $0$). The real number
$\sum_{j \ge 0} c_j 10^{-(j+1)} = 0.c_0c_1c_2\ldots$ is not normal in base $10$.

Source: John M. Campbell, *A Counterexample to a Purported Construction of Normal Numbers*,
Journal of Integer Sequences 29 (2026), Article 26.3.4, Theorem 8
(`jis-2026-26.3.4-thm-8`). -/
public theorem_wanted not_isNormalInBase_campbellConstant :
    ¬ NormalNumber.IsNormalInBase 10 campbellConstant

end

end MetaMathlibExt
