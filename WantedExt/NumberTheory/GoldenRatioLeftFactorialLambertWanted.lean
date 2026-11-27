/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio
public import MathlibExt.Analysis.SpecialFunctions.LambertWFunction
public import MathlibExt.NumberTheory.GoldenFactorialExponent
public import MathlibExt.NumberTheory.GoldenRatioLambertSequence
public import MathlibExt.NumberTheory.GoldenRatioLeftFactorialLambertKurepaPartialIntegralGoldenFactorialExponentBounds
public import MathlibExt.NumberTheory.GoldenRatioLeftFactorialLambertKurepaPartialIntegralLambertSequenceBounds

/-!
# The golden ratio, factorials, and the Lambert `W` function

Wanted statements from Petojević, Gorjanac Ranitović, Rastovac and Mandić on the golden
sequence `α n` (OEIS A214048), the counting sequence `d m` (OEIS A181716), and bounds for
the left factorial `!n = ∑_{k<n} k!` (OEIS A003422) by Kurepa's partial integral.
The statement `kurepaPartialIntegral_goldenFactorialExponent_bounds` is proved, and
`kurepaPartialIntegral` is defined, in
`MathlibExt.NumberTheory.GoldenRatioLeftFactorialLambertKurepaPartialIntegralGoldenFactorialExponentBounds`.
The statement `kurepaPartialIntegral_lambertSequence_bounds` is proved in
`MathlibExt.NumberTheory.GoldenRatioLeftFactorialLambertKurepaPartialIntegralLambertSequenceBounds`.

The paper's real sequence `a n = -(n - 1) W₋₁(-(1/(n-1)) (4/7)^(1/(n-1)))` uses the
lower real branch `W₋₁` of the Lambert `W` function. That branch is not defined in the
library, so each statement quantifies over `a` with `n - 1 ≤ a` and
`lambertMap (-a / (n - 1)) = -(1/(n-1)) (4/7)^(1/(n-1))`: writing `y = -a / (n - 1)`,
these say `y ≤ -1` and `y * exp y` equals the argument, which characterizes
`y = W₋₁(argument)` uniquely (`existsUnique_lambertMap_lower_preimage` in
`MathlibExt.Analysis.SpecialFunctions.LambertWFunction`). The same encoding is used for the
two-parameter sequence
`A n m` with `4/7` replaced by `4/(7m)`. `exists_lambertSequence` proves that such `a`
(and `A`) exist for `n ≥ 4`, so the statements are not vacuous.
-/

namespace MetaMathlibExt

open Real

@[expose] public section

/-- **Alternating-sign Fibonacci sequence.** The alternating-sign Fibonacci sequence
(OEIS A181716) is the integer sequence $(d_m)_{m \ge 0}$ defined by $d_0 = 0$, $d_1 = 1$ and
$d_{m+2} = d_{m+1} + d_m + (-1)^{m+2}$ for every natural number $m$.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Section 2.2 (definition before Lemma 3). -/
public def alternatingSignFibonacci : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | m + 2 => alternatingSignFibonacci (m + 1) + alternatingSignFibonacci m + (-1) ^ (m + 2)

/-- **Recurrence of the alternating-sign Fibonacci sequence.** For every natural number $m$,
the alternating-sign Fibonacci sequence $d$ satisfies $d_{m+2} = d_{m+1} + d_m + (-1)^{m+2}$.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Section 2.2. -/
public theorem alternatingSignFibonacci_add_two (m : ℕ) :
    alternatingSignFibonacci (m + 2) =
      alternatingSignFibonacci (m + 1) + alternatingSignFibonacci m + (-1) ^ (m + 2) :=
  rfl

/-- **First values of the alternating-sign Fibonacci sequence.** The alternating-sign Fibonacci
sequence $d$ satisfies $d_0 = 0$, $d_1 = 1$, $d_2 = 2$, $d_3 = 2$ and $d_4 = 5$.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Example 5. -/
public theorem alternatingSignFibonacci_small_values :
    alternatingSignFibonacci 0 = 0 ∧ alternatingSignFibonacci 1 = 1 ∧
      alternatingSignFibonacci 2 = 2 ∧ alternatingSignFibonacci 3 = 2 ∧
      alternatingSignFibonacci 4 = 5 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩ <;> norm_num [alternatingSignFibonacci]

/-- **Kurepa's partial integral vanishes at zero.** For every natural number $n$, Kurepa's partial
integral $K_n(x) = \int_0^x e^{-t} \sum_{k=0}^{n-1} t^k \, dt$ satisfies $K_n(0) = 0$.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Section 1. -/
public theorem kurepaPartialIntegral_zero (n : ℕ) : kurepaPartialIntegral n 0 = 0 := by
  simp [kurepaPartialIntegral]

/-- **Counting integers by their golden-ratio logarithm.** Let $d$ be the integer sequence with
$d(0) = 0$, $d(1) = 1$ and $d(m) = d(m-1) + d(m-2) + (-1)^m$ for $m \ge 2$, and let $\varphi$ be
the golden ratio. For every integer $m \ge 1$, the number of positive integers $n$ with
$\lfloor \log_\varphi n \rfloor = m$ equals $d(m)$.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Lemma 3 (`jis-2024-24.5.7-lem-3`). -/
public theorem_wanted ncard_floor_logb_goldenRatio_eq_alternatingSignFibonacci (m : ℕ)
    (hm : 1 ≤ m) :
    (({n : ℕ | 1 ≤ n ∧ ⌊Real.logb goldenRatio n⌋₊ = m}.ncard : ℕ) : ℤ) =
      alternatingSignFibonacci m

/-- **Existence of the Lambert sequences.** Let $h(y) = y e^y$ be the Lambert map. For every
natural number $n \ge 4$ and every real number $c$ with $0 < c \le 1$ there is a real number
$a \ge n - 1$ with
$$h\left(-\frac{a}{n-1}\right) = -\frac{1}{n-1} \, c^{1/(n-1)}.$$

Equivalently, $a = -(n-1) \, W_{-1}\left(-\frac{1}{n-1} c^{1/(n-1)}\right)$, where $W_{-1}$ is the
lower real branch of the Lambert W function. With $c = 4/7$ this is the paper's $a_n$, and with
$c = 4/(7m)$ for an integer $m \ge 1$ it is the paper's $A_{n,m}$.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Section 3.1 (the lower branch `W₋₁` defining `a n` and `A n m`). -/
public theorem exists_lambertSequence {n : ℕ} (hn : 4 ≤ n) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c ≤ 1) :
    ∃ a : ℝ, (n : ℝ) - 1 ≤ a ∧
      lambertMap (-a / ((n : ℝ) - 1)) = -(1 / ((n : ℝ) - 1)) * c ^ (1 / ((n : ℝ) - 1)) := by
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hcp : 0 < c ^ (1 / ((n : ℝ) - 1)) := Real.rpow_pos_of_pos hc0 _
  have hcle : c ^ (1 / ((n : ℝ) - 1)) ≤ 1 := Real.rpow_le_one hc0.le hc1 (by positivity)
  have he : (1 / 3 : ℝ) < Real.exp (-1) := by
    rw [Real.exp_neg, lt_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  have hq : 1 / ((n : ℝ) - 1) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hpos (by norm_num)]
    linarith
  obtain ⟨⟨y, hy⟩, hyx⟩ := (existsUnique_lambertMap_lower_preimage
    (x := -(1 / ((n : ℝ) - 1)) * c ^ (1 / ((n : ℝ) - 1)))
    (by nlinarith [one_div_pos.2 hpos]) (by nlinarith [one_div_pos.2 hpos])).exists
  refine ⟨-((n : ℝ) - 1) * y, by nlinarith, ?_⟩
  rw [show -(-((n : ℝ) - 1) * y) / ((n : ℝ) - 1) = y by field_simp]
  exact hyx

/-- **The golden factorial exponent exceeds the Lambert sequence.** Let $n > 4$ be an integer, let
$h(y) = y e^y$ be the Lambert map, and let $a$ be a real number with $a \ge n - 1$ and
$$h\left(-\frac{a}{n-1}\right) = -\frac{1}{n-1}\left(\frac{4}{7}\right)^{1/(n-1)}.$$
Then $a < \alpha(n)$, where $\alpha(n)$ is the least positive integer $m$ with $n! \le \varphi^m$
and $\varphi$ is the golden ratio.

The two conditions on $a$ say exactly that
$a = -(n-1)\, W_{-1}\left(-\frac{1}{n-1}\left(\frac{4}{7}\right)^{1/(n-1)}\right)$, where $W_{-1}$
is the lower real branch of the Lambert $W$ function; this is the paper's $a(n)$.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Theorem 6 (`jis-2024-24.5.7-thm-6`). -/
public theorem_wanted lambertSequence_lt_goldenFactorialExponent (n : ℕ) (hn : 4 < n)
    (a : ℝ) (ha : (n : ℝ) - 1 ≤ a)
    (hW : lambertMap (-a / ((n : ℝ) - 1)) =
      -(1 / ((n : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1))) :
    a < goldenFactorialExponent n

/-- **Partial exponential sums at the Lambert sequence.** Let $n \ge 5$ and $k$ be natural numbers
with $k < n - 2$, let $h(y) = y e^y$ be the Lambert map, and let $a$ be a real number with
$a \ge n - 1$ and
$$h\left(-\frac{a}{n-1}\right) = -\frac{1}{n-1}\left(\frac{4}{7}\right)^{1/(n-1)}.$$
Then
$$\sum_{t=0}^{k} \frac{a^t}{t!} < \frac{a^{k+1}}{(k+1)!}.$$

The two conditions on $a$ say exactly that
$a = -(n-1)\, W_{-1}\left(-\frac{1}{n-1}\left(\frac{4}{7}\right)^{1/(n-1)}\right)$, where $W_{-1}$
is the lower real branch of the Lambert $W$ function; this is the paper's $a(n)$.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Lemma 9 (`jis-2024-24.5.7-lem-9`). -/
public theorem_wanted sum_pow_div_factorial_lt_lambertSequence (n k : ℕ) (hn : 5 ≤ n)
    (hk : k < n - 2) (a : ℝ) (ha : (n : ℝ) - 1 ≤ a)
    (hW : lambertMap (-a / ((n : ℝ) - 1)) =
      -(1 / ((n : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1))) :
    ∑ t ∈ Finset.range (k + 1), a ^ t / (t.factorial : ℝ) <
      a ^ (k + 1) / ((k + 1).factorial : ℝ)

/-- **Two-parameter Lambert bounds for the left factorial.** Let $n \ge 5$ and $m \ge 1$ be
integers, let $!n = \sum_{k=0}^{n-1} k!$ be the left factorial, let
$K_n(x) = \int_0^x e^{-t} \sum_{k=0}^{n-1} t^k \, dt$ be Kurepa's partial integral, let
$h(y) = y e^y$ be the Lambert map, and let $A$ be a real number with $A \ge n - 1$ and
$$h\left(-\frac{A}{n-1}\right) = -\frac{1}{n-1}\left(\frac{4}{7m}\right)^{1/(n-1)}.$$
Then $K_n(A) < {!n} < K_n(A) + \frac{1}{m}$.

The two conditions on $A$ say exactly that
$A = -(n-1)\, W_{-1}\left(-\frac{1}{n-1}\left(\frac{4}{7m}\right)^{1/(n-1)}\right)$, where $W_{-1}$
is the lower real branch of the Lambert $W$ function; this is the paper's $A(n, m)$, and
$K_n(A)$ is its $B(n, m)$.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Theorem 14 (`jis-2024-24.5.7-thm-14`). -/
public theorem_wanted kurepaPartialIntegral_lambertSequence_two_bounds (n m : ℕ)
    (hn : 5 ≤ n) (hm : 1 ≤ m) (A : ℝ) (hA : (n : ℝ) - 1 ≤ A)
    (hW : lambertMap (-A / ((n : ℝ) - 1)) =
      -(1 / ((n : ℝ) - 1)) * (4 / (7 * m) : ℝ) ^ (1 / ((n : ℝ) - 1))) :
    kurepaPartialIntegral n A < ∑ k ∈ Finset.range n, (k.factorial : ℝ) ∧
      ∑ k ∈ Finset.range n, (k.factorial : ℝ) < kurepaPartialIntegral n A + 1 / m

/-- **Floor formulas for the left factorial.** Let $!n = \sum_{k=0}^{n-1} k!$ be the left
factorial, let $K_n(x) = \int_0^x e^{-t} \sum_{k=0}^{n-1} t^k \, dt$ be Kurepa's partial integral,
let $h(y) = y e^y$ be the Lambert map, and let $\alpha(n)$ be the least positive integer $m$ with
$n! \le \varphi^m$, where $\varphi$ is the golden ratio. Then the following hold.
(i) For every integer $n \ge 1$, $\lfloor K_n(\alpha(n)) \rfloor + 1 = {!n}$.
(ii) For every integer $n > 4$ and every real $a \ge n - 1$ with
$h(-\frac{a}{n-1}) = -\frac{1}{n-1} (\frac{4}{7})^{1/(n-1)}$, we have
$\lfloor K_n(a) \rfloor + 1 = {!n}$.
(iii) For all integers $n > 4$ and $m \ge 1$ and every real $A \ge n - 1$ with
$h(-\frac{A}{n-1}) = -\frac{1}{n-1} (\frac{4}{7m})^{1/(n-1)}$, we have
$\lfloor K_n(A) + \frac{1}{m} \rfloor = {!n}$.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Corollary 15 (`jis-2024-24.5.7-cor-15`). -/
public theorem_wanted leftFactorial_eq_floor_kurepaPartialIntegral :
    (∀ n : ℕ, 1 ≤ n →
      ⌊kurepaPartialIntegral n (goldenFactorialExponent n)⌋ + 1 =
        ∑ k ∈ Finset.range n, (k.factorial : ℤ)) ∧
    (∀ n : ℕ, 4 < n → ∀ a : ℝ, (n : ℝ) - 1 ≤ a →
      lambertMap (-a / ((n : ℝ) - 1)) =
        -(1 / ((n : ℝ) - 1)) * (4 / 7 : ℝ) ^ (1 / ((n : ℝ) - 1)) →
      ⌊kurepaPartialIntegral n a⌋ + 1 = ∑ k ∈ Finset.range n, (k.factorial : ℤ)) ∧
    (∀ n m : ℕ, 4 < n → 1 ≤ m → ∀ A : ℝ, (n : ℝ) - 1 ≤ A →
      lambertMap (-A / ((n : ℝ) - 1)) =
        -(1 / ((n : ℝ) - 1)) * (4 / (7 * m) : ℝ) ^ (1 / ((n : ℝ) - 1)) →
      ⌊kurepaPartialIntegral n A + 1 / m⌋ = ∑ k ∈ Finset.range n, (k.factorial : ℤ))

end

end MetaMathlibExt
