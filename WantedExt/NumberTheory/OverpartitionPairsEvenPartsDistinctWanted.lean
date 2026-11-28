/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct

/-!
# Congruences for `[j, k]`-overpartition pairs with even parts distinct (statements)

Statements from Adam Paksok and Nipen Saikia, *New Congruences for `[j, k]`-Overpartition Pairs
with Even Parts Distinct*, INTEGERS 26 (2026), Article A118. `bped_{j,k}(n)` is
`overpartitionPairEvenDistinct j k n`, the coefficient of `q^n` in the paper's generating
function (2). The paper's quotients `(… - 1)/2` are natural-number divisions of even numbers.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

/-- **Generating function of $[j, k]$-overpartition pairs with even parts distinct.** For natural
numbers $j$ and $k$, let $f_a = \prod_{m \ge 1} (1 - q^{am})$ be the Euler products. This
generating function is the integer power series
$f_4^2 \bigl(\prod_{i \ge 0} (1 + q^{j+ki})\bigr)^2 \, g$, where $g$ is the inverse of $f_1^2$
(whose constant coefficient is $1$) and the infinite products are taken in the coefficientwise
topology. In $q$-Pochhammer notation it is
$(q^4; q^4)_\infty^2 (-q^j; q^k)_\infty^2 / (q; q)_\infty^2$. It is used for $k \ge j \ge 1$.

Source: Adam Paksok and Nipen Saikia, *New Congruences for `[j, k]`-Overpartition Pairs with Even
Parts Distinct*, INTEGERS 26 (2026), Article A118, Section 1, Equation (2). -/
public noncomputable def overpartitionPairEvenDistinctGF (j k : ℕ) : ℤ⟦X⟧ :=
  qEulerProduct 4 ^ 2 * (∏' i : ℕ, (1 + X ^ (j + k * i))) ^ 2 *
    PowerSeries.invOfUnit (qEulerProduct 1 ^ 2) 1

/-- **The number of $[j, k]$-overpartition pairs with even parts distinct.** For natural numbers
$j$, $k$ and $n$, $\mathrm{bped}_{j,k}(n)$ is the integer coefficient of $q^n$ in the generating
function of $[j, k]$-overpartition pairs with even parts distinct.

Combinatorially, for $1 \le j \le k$, $\mathrm{bped}_{j,k}(n)$ is the number of
$[j, k]$-overpartition pairs of $n$ with even parts distinct, in which the first occurrence of
each distinct part congruent to $j$ modulo $k$ may be overlined.

Source: Adam Paksok and Nipen Saikia, *New Congruences for `[j, k]`-Overpartition Pairs with Even
Parts Distinct*, INTEGERS 26 (2026), Article A118, Section 1, Equation (2). -/
public noncomputable def overpartitionPairEvenDistinct (j k n : ℕ) : ℤ :=
  coeff n (overpartitionPairEvenDistinctGF j k)

/-- **Cleared form of the generating function of $[j, k]$-overpartition pairs with even parts
distinct.** For natural numbers $j$ and $k$, let $f_a = \prod_{m \ge 1} (1 - q^{am})$ be the
Euler products and let $G_{j,k}$ be the generating function of $[j, k]$-overpartition pairs with
even parts distinct. Then, as integer power series in $q$,
$G_{j,k} \, f_1^2 = f_4^2 \bigl(\prod_{i \ge 0} (1 + q^{j+ki})\bigr)^2$, where the infinite
product is taken in the coefficientwise topology. In $q$-Pochhammer notation this reads
$G_{j,k} \cdot (q; q)_\infty^2 = (q^4; q^4)_\infty^2 (-q^j; q^k)_\infty^2$.

Source: Adam Paksok and Nipen Saikia, *New Congruences for `[j, k]`-Overpartition Pairs with Even
Parts Distinct*, INTEGERS 26 (2026), Article A118, Section 1, Equation (2). -/
public theorem overpartitionPairEvenDistinctGF_mul_qEulerProduct_sq (j k : ℕ) :
    overpartitionPairEvenDistinctGF j k * qEulerProduct 1 ^ 2 =
      qEulerProduct 4 ^ 2 * (∏' i : ℕ, (1 + X ^ (j + k * i))) ^ 2 := by
  have h : constantCoeff (qEulerProduct 1 ^ 2) = ((1 : ℤˣ) : ℤ) := by
    rw [map_pow, constantCoeff_qEulerProduct le_rfl]
    simp
  rw [overpartitionPairEvenDistinctGF, mul_assoc, PowerSeries.invOfUnit_mul _ _ h, mul_one]

/-- **The count of overpartition pairs of $0$ with even parts distinct.** For natural numbers
$j \ge 1$ and $k \ge 1$, the number $\mathrm{bped}_{j,k}(0)$ of $[j, k]$-overpartition pairs of $0$
with even parts distinct equals $1$ (the pair of empty overpartitions).

Source: Adam Paksok and Nipen Saikia, *New Congruences for `[j, k]`-Overpartition Pairs with Even
Parts Distinct*, INTEGERS 26 (2026), Article A118, Section 1, Equation (2). -/
public theorem overpartitionPairEvenDistinct_zero (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    overpartitionPairEvenDistinct j k 0 = 1 := by
  have hmul : Multipliable fun i : ℕ => (1 : ℤ⟦X⟧) + X ^ (j + k * i) := by
    apply WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
    refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n => Filter.eventually_atTop.mpr ⟨n, ?_⟩
    intro m hm
    rw [order_X_pow]
    norm_cast
    nlinarith
  have hD : constantCoeff (∏' i : ℕ, ((1 : ℤ⟦X⟧) + X ^ (j + k * i))) = 1 := by
    rw [hmul.map_tprod _ (WithPiTopology.continuous_constantCoeff ℤ)]
    have h1 : ∀ i : ℕ, constantCoeff ((1 : ℤ⟦X⟧) + X ^ (j + k * i)) = 1 := fun i => by
      have : j + k * i ≠ 0 := by omega
      simp [zero_pow this]
    simp [h1]
  have hinv : constantCoeff (PowerSeries.invOfUnit (qEulerProduct 1 ^ 2) (1 : ℤˣ)) = 1 := by
    simp
  rw [overpartitionPairEvenDistinct, coeff_zero_eq_constantCoeff_apply,
    overpartitionPairEvenDistinctGF, map_mul, map_mul, map_pow, map_pow, hD,
    constantCoeff_qEulerProduct (by norm_num), hinv]
  simp

/-- **Paksok–Saikia congruences for $[3, 3]$-overpartition pairs (Theorem 1).** Let
$\mathrm{bped}_{j,k}(n)$ be the number of $[j, k]$-overpartition pairs of $n$ with even parts
distinct. Let $p > 5$ be a prime with Legendre symbol $\left(\frac{-6}{p}\right) = -1$, and let
$k, m, \alpha, \beta$ be natural numbers with $p \nmid m$. Then
$\mathrm{bped}_{3,3}\bigl(4 \cdot 3^{4\alpha+3} \cdot 5^{2\beta} p^{2k+1} m +
(7 \cdot 3^{4\alpha+2} \cdot 5^{2\beta} p^{2k+2} - 1)/2\bigr) \equiv 0 \pmod{16}$ and
$\mathrm{bped}_{3,3}\bigl(12 \cdot 5^{2\beta} p^{2k+1} m +
(7 \cdot 5^{2\beta} p^{2k+2} - 1)/2\bigr) \equiv 0 \pmod{8}$.

The paper prints $p^{2\alpha+2}$ in place of $p^{2k+2}$ in both congruences (its (6) and (7)); its
proof substitutes $n = p^{2k+1} m + 7(p^{2k+2} - 1)/24$, which gives $p^{2k+2}$, and the printed
exponent fails: at $p = 13$, $k = 1$, $\alpha = \beta = 0$, $m = 2$ the printed argument of the
second congruence is $53319$, and $\mathrm{bped}_{3,3}(53319) \equiv 4 \pmod{8}$.

Source: Adam Paksok and Nipen Saikia, *New Congruences for `[j, k]`-Overpartition Pairs with Even
Parts Distinct*, INTEGERS 26 (2026), Article A118, Theorem 1
(`integers-2026-A118-thm-1`). -/
public theorem_wanted overpartitionPairEvenDistinct_three_three_congr_neg_six
    (p : ℕ) [Fact p.Prime] (hp : 5 < p) (hleg : legendreSym p (-6) = -1)
    (k m α β : ℕ) (hm : ¬ p ∣ m) :
    (16 : ℤ) ∣ overpartitionPairEvenDistinct 3 3
        (4 * 3 ^ (4 * α + 3) * 5 ^ (2 * β) * p ^ (2 * k + 1) * m +
          (7 * 3 ^ (4 * α + 2) * 5 ^ (2 * β) * p ^ (2 * k + 2) - 1) / 2) ∧
      (8 : ℤ) ∣ overpartitionPairEvenDistinct 3 3
        (12 * 5 ^ (2 * β) * p ^ (2 * k + 1) * m + (7 * 5 ^ (2 * β) * p ^ (2 * k + 2) - 1) / 2)

/-- **Paksok–Saikia congruences for $[3, 3]$- and $[3, 6]$-overpartition pairs (Theorem 2).** Let
$\mathrm{bped}_{j,k}(n)$ be the number of $[j, k]$-overpartition pairs of $n$ with even parts
distinct. Let $p \ge 5$ be a prime with Legendre symbol $\left(\frac{-2}{p}\right) = -1$, and let
$k, m, \alpha, \beta$ be natural numbers with $p \nmid m$. Then
$\mathrm{bped}_{3,3}\bigl(4 \cdot 3^{4\alpha+3} \cdot 5^{2\beta} p^{2k+1} m +
(11 \cdot 3^{4\alpha+2} \cdot 5^{2\beta} p^{2k+2} - 1)/2\bigr) \equiv 0 \pmod{16}$,
$\mathrm{bped}_{3,3}\bigl(12 \cdot 5^{2\beta} p^{2k+1} m +
(11 \cdot 5^{2\beta} p^{2k+2} - 1)/2\bigr) \equiv 0 \pmod{4}$,
$\mathrm{bped}_{3,6}\bigl(3^{4\alpha+2} \cdot 5^{2\beta} p^{2k+1} (24m + 11p)\bigr) \equiv 0
\pmod{32}$ and
$\mathrm{bped}_{3,6}\bigl(3 \cdot 5^{2\beta} p^{2k+1} (24m + 11p)\bigr) \equiv 0 \pmod{32}$.

The paper prints $p^{2\alpha+2}$ in place of $p^{2k+2}$ in the first two congruences (its (10) and
(11)); the substitution in its proof gives $p^{2k+2}$, and the printed exponent fails: at $p = 5$,
$k = 1$, $\alpha = \beta = 0$, $m = 1$ the printed arguments are $14737$ and $1637$, and
$\mathrm{bped}_{3,3}(14737) \equiv 8 \pmod{16}$, $\mathrm{bped}_{3,3}(1637) \equiv 2 \pmod{4}$.

Source: Adam Paksok and Nipen Saikia, *New Congruences for `[j, k]`-Overpartition Pairs with Even
Parts Distinct*, INTEGERS 26 (2026), Article A118, Theorem 2
(`integers-2026-A118-thm-2`). -/
public theorem_wanted overpartitionPairEvenDistinct_congr_neg_two_eleven
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hleg : legendreSym p (-2) = -1)
    (k m α β : ℕ) (hm : ¬ p ∣ m) :
    (16 : ℤ) ∣ overpartitionPairEvenDistinct 3 3
        (4 * 3 ^ (4 * α + 3) * 5 ^ (2 * β) * p ^ (2 * k + 1) * m +
          (11 * 3 ^ (4 * α + 2) * 5 ^ (2 * β) * p ^ (2 * k + 2) - 1) / 2) ∧
      (4 : ℤ) ∣ overpartitionPairEvenDistinct 3 3
        (12 * 5 ^ (2 * β) * p ^ (2 * k + 1) * m + (11 * 5 ^ (2 * β) * p ^ (2 * k + 2) - 1) / 2) ∧
      (32 : ℤ) ∣ overpartitionPairEvenDistinct 3 6
        (3 ^ (4 * α + 2) * 5 ^ (2 * β) * p ^ (2 * k + 1) * (24 * m + 11 * p)) ∧
      (32 : ℤ) ∣ overpartitionPairEvenDistinct 3 6
        (3 * 5 ^ (2 * β) * p ^ (2 * k + 1) * (24 * m + 11 * p))

/-- **Paksok–Saikia congruences for $[3, 3]$- and $[3, 6]$-overpartition pairs (Theorem 3).** Let
$\mathrm{bped}_{j,k}(n)$ be the number of $[j, k]$-overpartition pairs of $n$ with even parts
distinct. Let $p \ge 5$ be a prime with Legendre symbol $\left(\frac{-2}{p}\right) = -1$, and let
$k, m, \alpha, \beta$ be natural numbers with $p \nmid m$. Then
$\mathrm{bped}_{3,3}\bigl(4 \cdot 3^{4\alpha+3} \cdot 5^{2\beta} p^{2k+1} m +
(19 \cdot 3^{4\alpha+2} \cdot 5^{2\beta} p^{2k+2} - 1)/2\bigr) \equiv 0 \pmod{16}$,
$\mathrm{bped}_{3,3}\bigl(12 \cdot 5^{2\beta} p^{2k+1} m +
(19 \cdot 5^{2\beta} p^{2k+2} - 1)/2\bigr) \equiv 0 \pmod{8}$,
$\mathrm{bped}_{3,6}\bigl(3^{4\alpha+2} \cdot 5^{2\beta} p^{2k+1} (24m + 19p)\bigr) \equiv 0
\pmod{32}$ and
$\mathrm{bped}_{3,6}\bigl(3 \cdot 5^{2\beta} p^{2k+1} (24m + 19p)\bigr) \equiv 0 \pmod{32}$.

The paper prints $p^{2\alpha+2}$ in place of $p^{2k+2}$ in the first two congruences (its (16) and
(17)); the substitution in its proof gives $p^{2k+2}$, and the printed exponent fails: at $p = 5$,
$k = 1$, $\alpha = \beta = 0$, $m = 1$ the printed arguments are $15637$ and $1737$, and
$\mathrm{bped}_{3,3}(15637) \equiv 8 \pmod{16}$, $\mathrm{bped}_{3,3}(1737) \equiv 4 \pmod{8}$.

Source: Adam Paksok and Nipen Saikia, *New Congruences for `[j, k]`-Overpartition Pairs with Even
Parts Distinct*, INTEGERS 26 (2026), Article A118, Theorem 3
(`integers-2026-A118-thm-3`). -/
public theorem_wanted overpartitionPairEvenDistinct_congr_neg_two_nineteen
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hleg : legendreSym p (-2) = -1)
    (k m α β : ℕ) (hm : ¬ p ∣ m) :
    (16 : ℤ) ∣ overpartitionPairEvenDistinct 3 3
        (4 * 3 ^ (4 * α + 3) * 5 ^ (2 * β) * p ^ (2 * k + 1) * m +
          (19 * 3 ^ (4 * α + 2) * 5 ^ (2 * β) * p ^ (2 * k + 2) - 1) / 2) ∧
      (8 : ℤ) ∣ overpartitionPairEvenDistinct 3 3
        (12 * 5 ^ (2 * β) * p ^ (2 * k + 1) * m + (19 * 5 ^ (2 * β) * p ^ (2 * k + 2) - 1) / 2) ∧
      (32 : ℤ) ∣ overpartitionPairEvenDistinct 3 6
        (3 ^ (4 * α + 2) * 5 ^ (2 * β) * p ^ (2 * k + 1) * (24 * m + 19 * p)) ∧
      (32 : ℤ) ∣ overpartitionPairEvenDistinct 3 6
        (3 * 5 ^ (2 * β) * p ^ (2 * k + 1) * (24 * m + 19 * p))

/-- **Paksok–Saikia congruences for $[3, 3]$- and $[3, 6]$-overpartition pairs (Theorem 4).** Let
$\mathrm{bped}_{j,k}(n)$ be the number of $[j, k]$-overpartition pairs of $n$ with even parts
distinct. Let $p \ge 5$ be a prime with Legendre symbol $\left(\frac{-1}{p}\right) = -1$, and let
$k, m, \alpha, \gamma$ be natural numbers with $p \nmid m$. Then
$\mathrm{bped}_{3,3}\bigl(4 \cdot 3^{4\alpha+2} \cdot 7^{2\gamma} p^{2k+1} m +
(5 \cdot 3^{4\alpha+1} \cdot 7^{2\gamma} p^{2k+2} - 1)/2\bigr) \equiv 0 \pmod{8}$,
$\mathrm{bped}_{3,6}\bigl(3^{4\alpha+2} \cdot 7^{2\gamma} p^{2k+1} (24m + 5p)\bigr) \equiv 0
\pmod{16}$ and
$\mathrm{bped}_{3,6}\bigl(3 \cdot 7^{2\gamma} p^{2k+1} (24m + 5p)\bigr) \equiv 0 \pmod{16}$.

The paper allows $p \ge 3$, but its proof needs $p \nmid 24m + 5p$, which fails for $p = 3$, and
all three congruences fail there: at $k = \alpha = \gamma = 0$, $m = 1$ one has
$\mathrm{bped}_{3,3}(175) \equiv 4 \pmod{8}$, $\mathrm{bped}_{3,6}(1053) \equiv 8 \pmod{16}$ and
$\mathrm{bped}_{3,6}(351) \equiv 8 \pmod{16}$; so $p \ge 5$ is assumed. The paper also prints
$p^{2\alpha+2}$ in place of $p^{2k+2}$ in the first congruence (its (22)); the substitution in its
proof gives $p^{2k+2}$, and the printed exponent fails: at $p = 7$, $k = 1$, $\alpha = \gamma = 0$,
$m = 1$ the printed argument is $12715$, and $\mathrm{bped}_{3,3}(12715) \equiv 4 \pmod{8}$.

Source: Adam Paksok and Nipen Saikia, *New Congruences for `[j, k]`-Overpartition Pairs with Even
Parts Distinct*, INTEGERS 26 (2026), Article A118, Theorem 4
(`integers-2026-A118-thm-4`). -/
public theorem_wanted overpartitionPairEvenDistinct_congr_neg_one_five
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hleg : legendreSym p (-1) = -1)
    (k m α γ : ℕ) (hm : ¬ p ∣ m) :
    (8 : ℤ) ∣ overpartitionPairEvenDistinct 3 3
        (4 * 3 ^ (4 * α + 2) * 7 ^ (2 * γ) * p ^ (2 * k + 1) * m +
          (5 * 3 ^ (4 * α + 1) * 7 ^ (2 * γ) * p ^ (2 * k + 2) - 1) / 2) ∧
      (16 : ℤ) ∣ overpartitionPairEvenDistinct 3 6
        (3 ^ (4 * α + 2) * 7 ^ (2 * γ) * p ^ (2 * k + 1) * (24 * m + 5 * p)) ∧
      (16 : ℤ) ∣ overpartitionPairEvenDistinct 3 6
        (3 * 7 ^ (2 * γ) * p ^ (2 * k + 1) * (24 * m + 5 * p))

/-- **Paksok–Saikia congruences for $[3, 3]$- and $[3, 6]$-overpartition pairs (Theorem 5).** Let
$\mathrm{bped}_{j,k}(n)$ be the number of $[j, k]$-overpartition pairs of $n$ with even parts
distinct. Let $p \ge 5$ be a prime with Legendre symbol $\left(\frac{-3}{p}\right) = -1$, and let
$k, m, \alpha, \beta$ be natural numbers with $p \nmid m$. Then
$\mathrm{bped}_{3,3}\bigl(4 \cdot 3^{4\alpha+2} \cdot 5^{2\beta} p^{2k+1} m +
(13 \cdot 3^{4\alpha+1} \cdot 5^{2\beta} p^{2k+2} - 1)/2\bigr) \equiv 0 \pmod{8}$,
$\mathrm{bped}_{3,6}\bigl(3^{4\alpha+2} \cdot 5^{2\beta} p^{2k+1} (24m + 13p)\bigr) \equiv 0
\pmod{16}$ and
$\mathrm{bped}_{3,6}\bigl(3 \cdot 5^{2\beta} p^{2k+1} (24m + 13p)\bigr) \equiv 0 \pmod{16}$.

The paper prints $p^{2\alpha+2}$ in place of $p^{2k+2}$ in the first congruence (its (27)); the
substitution in its proof gives $p^{2k+2}$, and the printed exponent fails: at $p = 5$, $k = 1$,
$\alpha = \beta = 0$, $m = 3$ the printed argument is $13987$, and
$\mathrm{bped}_{3,3}(13987) \equiv 4 \pmod{8}$.

Source: Adam Paksok and Nipen Saikia, *New Congruences for `[j, k]`-Overpartition Pairs with Even
Parts Distinct*, INTEGERS 26 (2026), Article A118, Theorem 5
(`integers-2026-A118-thm-5`). -/
public theorem_wanted overpartitionPairEvenDistinct_congr_neg_three_thirteen
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hleg : legendreSym p (-3) = -1)
    (k m α β : ℕ) (hm : ¬ p ∣ m) :
    (8 : ℤ) ∣ overpartitionPairEvenDistinct 3 3
        (4 * 3 ^ (4 * α + 2) * 5 ^ (2 * β) * p ^ (2 * k + 1) * m +
          (13 * 3 ^ (4 * α + 1) * 5 ^ (2 * β) * p ^ (2 * k + 2) - 1) / 2) ∧
      (16 : ℤ) ∣ overpartitionPairEvenDistinct 3 6
        (3 ^ (4 * α + 2) * 5 ^ (2 * β) * p ^ (2 * k + 1) * (24 * m + 13 * p)) ∧
      (16 : ℤ) ∣ overpartitionPairEvenDistinct 3 6
        (3 * 5 ^ (2 * β) * p ^ (2 * k + 1) * (24 * m + 13 * p))

/-- **Paksok–Saikia congruences for $[3, 6]$-overpartition pairs (Theorem 6).** Let
$\mathrm{bped}_{j,k}(n)$ be the number of $[j, k]$-overpartition pairs of $n$ with even parts
distinct. Let $p \ge 5$ be a prime with Legendre symbol $\left(\frac{-1}{p}\right) = -1$, and let
$k, m, \alpha$ be natural numbers with $p \nmid m$. Then
$\mathrm{bped}_{3,6}\bigl(3^{4\alpha+2} p^{2k+1} (12m + 5p)\bigr) \equiv 0 \pmod{16}$ and
$\mathrm{bped}_{3,6}\bigl(3 p^{2k+1} (12m + 5p)\bigr) \equiv 0 \pmod{16}$.

The paper allows $p \ge 3$, but its proof needs $p \nmid 24m + 10p$, which fails for $p = 3$, and
both congruences fail there: at $k = \alpha = 0$, $m = 1$ one has
$\mathrm{bped}_{3,6}(729) \equiv 12 \pmod{16}$ and $\mathrm{bped}_{3,6}(243) \equiv 12 \pmod{16}$;
so $p \ge 5$ is assumed. The paper's unused quantifier $\beta$ is dropped.

Source: Adam Paksok and Nipen Saikia, *New Congruences for `[j, k]`-Overpartition Pairs with Even
Parts Distinct*, INTEGERS 26 (2026), Article A118, Theorem 6
(`integers-2026-A118-thm-6`). -/
public theorem_wanted overpartitionPairEvenDistinct_three_six_congr_neg_one_five
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (hleg : legendreSym p (-1) = -1)
    (k m α : ℕ) (hm : ¬ p ∣ m) :
    (16 : ℤ) ∣ overpartitionPairEvenDistinct 3 6
        (3 ^ (4 * α + 2) * p ^ (2 * k + 1) * (12 * m + 5 * p)) ∧
      (16 : ℤ) ∣ overpartitionPairEvenDistinct 3 6 (3 * p ^ (2 * k + 1) * (12 * m + 5 * p))

end

end MetaMathlibExt
