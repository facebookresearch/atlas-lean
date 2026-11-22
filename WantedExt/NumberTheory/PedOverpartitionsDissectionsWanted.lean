/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.PowerSeries.Inverse
public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
public import MathlibExt.NumberTheory.ModularForms.JacobiTheta.Ramanujan

/-!
# `[j, k]`-overpartitions with even parts distinct (Harishkumar, Menezes, Mahadeva Naika)

Statements from Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika,
*On [j, k]-Overpartitions with Even Parts Distinct*, INTEGERS 25 (2025), Article A69.

In the paper's notation `f_k = (q^k; q^k)_∞`, written here `qPochhammerInfRaw (q^k) (q^k)`, and
`f(a, b)` is Ramanujan's general theta function, written `ramanujanThetaRaw a b`. For `‖q‖ < 1`
every product and theta series below converges, so the raw values are the classical ones.

The remaining statements are identities and congruences of integer power series, with
`f_k = qEulerProduct k`, written `𝔣 k`. `ped_{j,k}(n)` counts the `[j, k]`-overpartitions of `n`
with even parts distinct (even parts distinct; the first occurrence of each distinct part
congruent to `j` modulo `k` may be overlined). Its generating function is the paper's (2),
`∑ ped_{j,k}(n) q^n = (q^4; q^4)_∞ (-q^j; q^k)_∞ / (q; q)_∞`; for `(j, k) = (9, 9)` and `(9, 18)`
this is `f_4 f_18 / (f_1 f_9)` and `f_4 f_18^2 / (f_1 f_9 f_36)`, and `ped_{9,9}`, `ped_{9,18}`
are defined as the coefficients of these quotients in `ℤ⟦X⟧` (the denominators have constant
coefficient `1`). Quotients of `f_k` are stated with denominators cleared, and a congruence
between generating functions is stated coefficientwise.
-/

open PowerSeries

namespace MetaMathlibExt

open MetaMathlibExt.QPochhammer

@[expose] public section

/-- **Ramanujan's 5-dissection of Euler's product.** Let $q$ be a complex number with
$|q| < 1$. For $k \ge 1$ let $f_k = (q^k; q^k)_\infty = \prod_{n \ge 0} (1 - q^k q^{kn})$, and
for complex $a$, $b$ with $|a|, |b| < 1$ let $f(a, b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2}
b^{n(n-1)/2}$ be Ramanujan's general theta function; all these products and series converge,
so the raw infinite product and the raw theta sum take these values. For $|x| < 1$ put
$R(x) = f(-x, -x^4) / f(-x^2, -x^3)$. Then
$f_1 = f_{25} \left( R(q^5)^{-1} - q - q^2 R(q^5) \right)$.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Lemma 5 (`integers-2025-A69-lem-5`). -/
public theorem_wanted qPochhammerInf_five_dissection (q : ℂ) (hq : ‖q‖ < 1) :
    let R : ℂ → ℂ := fun x => ramanujanThetaRaw (-x) (-x ^ 4) / ramanujanThetaRaw (-x ^ 2) (-x ^ 3)
    qPochhammerInfRaw q q =
      qPochhammerInfRaw (q ^ 25) (q ^ 25) * ((R (q ^ 5))⁻¹ - q - q ^ 2 * R (q ^ 5))

/-- **Ramanujan's 7-dissection of Euler's product.** Let $q$ be a complex number with
$|q| < 1$. For $k \ge 1$ let $f_k = (q^k; q^k)_\infty = \prod_{n \ge 0} (1 - q^k q^{kn})$, and
for complex $a$, $b$ with $|a|, |b| < 1$ let $f(a, b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2}
b^{n(n-1)/2}$ be Ramanujan's general theta function; all these products and series converge,
so the raw infinite product and the raw theta sum take these values. For $|x| < 1$ put
$A(x) = f(-x^3, -x^4)$, $B(x) = f(-x^2, -x^5)$ and $C(x) = f(-x, -x^6)$. Then
$f_1 = f_{49} \left( B(q^7)/C(q^7) - q A(q^7)/B(q^7) - q^2 + q^5 C(q^7)/A(q^7) \right)$.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Lemma 6 (`integers-2025-A69-lem-6`). -/
public theorem_wanted qPochhammerInf_seven_dissection (q : ℂ) (hq : ‖q‖ < 1) :
    let A : ℂ → ℂ := fun x => ramanujanThetaRaw (-x ^ 3) (-x ^ 4)
    let B : ℂ → ℂ := fun x => ramanujanThetaRaw (-x ^ 2) (-x ^ 5)
    let C : ℂ → ℂ := fun x => ramanujanThetaRaw (-x) (-x ^ 6)
    qPochhammerInfRaw q q =
      qPochhammerInfRaw (q ^ 49) (q ^ 49) *
        (B (q ^ 7) / C (q ^ 7) - q * A (q ^ 7) / B (q ^ 7) - q ^ 2 + q ^ 5 * C (q ^ 7) / A (q ^ 7))


local notation "𝔣" => qEulerProduct

/-- **The generating series for $\mathrm{ped}_{9,9}$.** For $k \ge 1$ let
$f_k = \prod_{m \ge 1} (1 - q^{km})$, an integer power series in $q$ with constant coefficient $1$.
This is the integer power series
$$\frac{f_4 f_{18}}{f_1 f_9},$$
where the inverse of $f_1 f_9$ is taken in the ring of integer power series. For a natural number
$n$, its coefficient of $q^n$ is denoted $\mathrm{ped}_{9,9}(n)$.

By the source's equation (2), this is the generating function of the $[9, 9]$-overpartitions with
even parts distinct: partitions whose even parts are distinct, in which the first occurrence of
each part divisible by $9$ may be overlined.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, equations (2) and (22). -/
noncomputable def pedNineNineSeries : ℤ⟦X⟧ :=
  𝔣 4 * 𝔣 18 * invOfUnit (𝔣 1 * 𝔣 9) 1

/-- **The partition function $\mathrm{ped}_{9,9}$.** For $k \ge 1$ let
$f_k = \prod_{m \ge 1} (1 - q^{km})$, an integer power series in $q$ with constant coefficient $1$.
For a natural number $n$, $\mathrm{ped}_{9,9}(n)$ is the integer coefficient of $q^n$ in the power
series $f_4 f_{18} / (f_1 f_9)$.

By the source's equation (2), $\mathrm{ped}_{9,9}(n)$ is the number of $[9, 9]$-overpartitions of
$n$ with even parts distinct.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, equations (2) and (22). -/
noncomputable def pedNineNine (n : ℕ) : ℤ :=
  coeff n pedNineNineSeries

/-- **The generating series for $\mathrm{ped}_{9,18}$.** For $k \ge 1$ let
$f_k = \prod_{m \ge 1} (1 - q^{km})$, an integer power series in $q$ with constant coefficient $1$.
This is the integer power series
$$\frac{f_4 f_{18}^2}{f_1 f_9 f_{36}},$$
where the inverse of $f_1 f_9 f_{36}$ is taken in the ring of integer power series. For a
natural number $n$, its coefficient of $q^n$ is denoted $\mathrm{ped}_{9,18}(n)$.

By the source's equation (2), this is the generating function of the $[9, 18]$-overpartitions with
even parts distinct: partitions whose even parts are distinct, in which the first occurrence of
each part congruent to $9$ modulo $18$ may be overlined.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, equations (2) and (77). -/
noncomputable def pedNineEighteenSeries : ℤ⟦X⟧ :=
  𝔣 4 * 𝔣 18 ^ 2 * invOfUnit (𝔣 1 * 𝔣 9 * 𝔣 36) 1

/-- **The partition function $\mathrm{ped}_{9,18}$.** For $k \ge 1$ let
$f_k = \prod_{m \ge 1} (1 - q^{km})$, an integer power series in $q$ with constant coefficient $1$.
For a natural number $n$, $\mathrm{ped}_{9,18}(n)$ is the integer coefficient of $q^n$ in the power
series $f_4 f_{18}^2 / (f_1 f_9 f_{36})$.

By the source's equation (2), $\mathrm{ped}_{9,18}(n)$ is the number of $[9, 18]$-overpartitions of
$n$ with even parts distinct.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, equations (2) and (77). -/
noncomputable def pedNineEighteen (n : ℕ) : ℤ :=
  coeff n pedNineEighteenSeries

/-- **Generating function identity for $\mathrm{ped}_{9,9}$.** For $k \ge 1$ let
$f_k = \prod_{m \ge 1} (1 - q^{km})$, an integer power series in $q$, and let
$\mathrm{ped}_{9,9}(n)$ be the coefficient of $q^n$ in $f_4 f_{18} / (f_1 f_9)$. Then, as integer
power series in $q$,
$$f_1 f_9 \sum_{n \ge 0} \mathrm{ped}_{9,9}(n) q^n = f_4 f_{18}.$$

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, equation (22). -/
theorem pedNineNine_generatingFunction :
    𝔣 1 * 𝔣 9 * PowerSeries.mk pedNineNine = 𝔣 4 * 𝔣 18 := by
  have hmk : PowerSeries.mk pedNineNine = pedNineNineSeries := by
    ext n
    simp [pedNineNine]
  have hc : constantCoeff (𝔣 1 * 𝔣 9) = ((1 : ℤˣ) : ℤ) := by
    simp [constantCoeff_qEulerProduct (le_refl 1),
      constantCoeff_qEulerProduct (by norm_num : 1 ≤ 9)]
  rw [hmk, pedNineNineSeries, mul_left_comm, mul_invOfUnit _ _ hc, mul_one]

/-- **Product identity for the [9, 18]-overpartition generating function.** Let
$\mathrm{ped}_{9,18}(n)$ be the number of $[9, 18]$-overpartitions of $n$ with even parts
distinct, and let $f_k = \prod_{m \ge 1} (1 - q^{km})$. Then, as integer power series in $q$,
$f_1 f_9 f_{36} \sum_{n \ge 0} \mathrm{ped}_{9,18}(n) q^n = f_4 f_{18}^2$.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, equation (77). -/
theorem pedNineEighteen_generatingFunction :
    𝔣 1 * 𝔣 9 * 𝔣 36 * PowerSeries.mk pedNineEighteen = 𝔣 4 * 𝔣 18 ^ 2 := by
  have hmk : PowerSeries.mk pedNineEighteen = pedNineEighteenSeries := by
    ext n
    simp [pedNineEighteen]
  have hc : constantCoeff (𝔣 1 * 𝔣 9 * 𝔣 36) = ((1 : ℤˣ) : ℤ) := by
    simp [constantCoeff_qEulerProduct (le_refl 1),
      constantCoeff_qEulerProduct (by norm_num : 1 ≤ 9),
      constantCoeff_qEulerProduct (by norm_num : 1 ≤ 36)]
  rw [hmk, pedNineEighteenSeries, mul_left_comm, mul_invOfUnit _ _ hc, mul_one]

/-- **Values of $\mathrm{ped}_{9,9}$ and $\mathrm{ped}_{9,18}$ at $0$.** For $k \ge 1$ let
$f_k = \prod_{m \ge 1} (1 - q^{km})$, an integer power series in $q$, and let
$\mathrm{ped}_{9,9}(n)$ and $\mathrm{ped}_{9,18}(n)$ be the coefficients of $q^n$ in
$f_4 f_{18} / (f_1 f_9)$ and in $f_4 f_{18}^2 / (f_1 f_9 f_{36})$. Then
$\mathrm{ped}_{9,9}(0) = \mathrm{ped}_{9,18}(0) = 1$.

Both values count the empty overpartition.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, equations (22) and (77). -/
theorem pedNineNine_zero_and_pedNineEighteen_zero :
    pedNineNine 0 = 1 ∧ pedNineEighteen 0 = 1 := by
  have h1 := congrArg (coeff 0) pedNineNine_generatingFunction
  have h2 := congrArg (coeff 0) pedNineEighteen_generatingFunction
  simp only [coeff_zero_eq_constantCoeff, map_mul, map_pow,
    constantCoeff_qEulerProduct (le_refl 1), constantCoeff_qEulerProduct (by norm_num : 1 ≤ 4),
    constantCoeff_qEulerProduct (by norm_num : 1 ≤ 9),
    constantCoeff_qEulerProduct (by norm_num : 1 ≤ 18),
    constantCoeff_qEulerProduct (by norm_num : 1 ≤ 36), one_pow, one_mul] at h1 h2
  exact ⟨by simpa using h1, by simpa using h2⟩

/-- **Chan's matrix.** Chan's matrix $(m_{i,j})_{i,j \ge 1}$ is the integer matrix with first
column $m_{1,1} = 3$, $m_{2,1} = 2$, $m_{3,1} = 1$ and $m_{i,1} = 0$ for $i \ge 4$, and with
$m_{i,j} = 9 m_{i-1,j-1} + 3 m_{i-2,j-1} + m_{i-3,j-1}$ for $i \ge 1$ and $j \ge 2$, where
entries with row index $\le 0$ are taken to be $0$.

The formalization indexes the matrix by all natural numbers, with row $0$ and column $0$ equal
to $0$.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Section 2 (from H. C. Chan, Int. J. Number
Theory 6 (2010), (11)-(19)). -/
def chanCubicMatrix : ℕ → ℕ → ℤ
  | _, 0 => 0
  | i, 1 => if i = 1 then 3 else if i = 2 then 2 else if i = 3 then 1 else 0
  | i, j + 2 =>
      9 * chanCubicMatrix (i - 1) (j + 1) + 3 * chanCubicMatrix (i - 2) (j + 1) +
        chanCubicMatrix (i - 3) (j + 1)

/-- **First six rows of Chan's matrix.** The upper left $6 \times 6$ block of Chan's matrix
$(m_{i,j})_{i,j \ge 1}$ is lower triangular, and its rows up to the diagonal are $(3)$,
$(2, 27)$, $(1, 27, 243)$, $(0, 18, 324, 2187)$, $(0, 5, 270, 3645, 19683)$ and
$(0, 1, 126, 3645, 39366, 177147)$: for $1 \le j \le i \le 6$, $m_{i,j}$ is the $j$th entry of
the $i$th listed row, and $m_{i,j} = 0$ for $1 \le i < j \le 6$.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Section 2. -/
theorem chanCubicMatrix_first_rows :
    (List.range 6).map (fun i => (List.range 6).map fun j => chanCubicMatrix (i + 1) (j + 1)) =
      [[3, 0, 0, 0, 0, 0], [2, 27, 0, 0, 0, 0], [1, 27, 243, 0, 0, 0],
        [0, 18, 324, 2187, 0, 0], [0, 5, 270, 3645, 19683, 0],
        [0, 1, 126, 3645, 39366, 177147]] := by
  decide

/-- **Coefficient vectors from Chan's matrix.** Let $(m_{i,j})_{i,j \ge 1}$ be Chan's matrix, and
for $i, j \ge 1$ let $a_{i,j} = m_{4i-3,i+j-1}$ and $b_{i,j} = m_{4i-1,i+j-1}$ be the entries of
the infinite matrices $A$ and $B$. The coefficient vectors
$X_\alpha = (x_{\alpha,1}, x_{\alpha,2}, \dots)$ of integers, for $\alpha \ge 0$, are defined by
$X_0 = (1, 0, 0, \dots)$ and, for $j \ge 1$, $x_{\alpha+1,j} = \sum_{i=1}^{3^\alpha} x_{\alpha,i}
a_{i,j}$ if $\alpha$ is even and $x_{\alpha+1,j} = \sum_{i=1}^{3^\alpha} x_{\alpha,i} b_{i,j}$ if
$\alpha$ is odd.

Since Chan's matrix is lower triangular, row $i$ of $A$ or $B$ vanishes beyond column $3i$, so by
induction $x_{\alpha,i} = 0$ for $i > 3^\alpha$; hence $X_{\alpha+1} = X_\alpha A$ for even
$\alpha$ and $X_{\alpha+1} = X_\alpha B$ for odd $\alpha$.

The formalization indexes the vectors from $0$: its value at $(\alpha, i)$ is $x_{\alpha,i+1}$.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Section 2, equations (3)-(4), and
Theorem 8. -/
def cubicCoeffVector : ℕ → ℕ → ℤ
  | 0, i => if i = 0 then 1 else 0
  | α + 1, j => ∑ i ∈ Finset.range (3 ^ α), cubicCoeffVector α i *
      (if Even α then chanCubicMatrix (4 * i + 1) (i + j + 1)
        else chanCubicMatrix (4 * i + 3) (i + j + 1))

/-- **Initial values of the cubic coefficient vectors.** The coefficient vectors
$X_\alpha = (x_{\alpha,1}, x_{\alpha,2}, \dots)$ built from Chan's matrix satisfy
$(x_{1,1}, \dots, x_{1,5}) = (3, 0, 0, 0, 0)$ and
$(x_{2,1}, \dots, x_{2,5}) = (3, 81, 729, 0, 0)$.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Theorem 8. -/
theorem cubicCoeffVector_one_two :
    (List.range 5).map (cubicCoeffVector 1) = [3, 0, 0, 0, 0] ∧
      (List.range 5).map (cubicCoeffVector 2) = [3, 81, 729, 0, 0] := by
  decide

/-- **The 2-dissection of $f_1^4$.** For $k \ge 1$ let $f_k = \prod_{m \ge 1} (1 - q^{km})$, an
integer power series in $q$. Then
$$f_1^4 f_2^2 f_4^2 f_8^4 = f_4^{12} - 4 q f_2^4 f_8^8.$$
Dividing by $f_2^2 f_4^2 f_8^4$ gives
$f_1^4 = \frac{f_4^{10}}{f_2^2 f_8^4} - 4q \frac{f_2^2 f_8^4}{f_4^2}$.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Lemma 1, (7)
(`integers-2025-A69-lem-1`). -/
public theorem_wanted qEulerProduct_fourth_two_dissection :
    𝔣 1 ^ 4 * 𝔣 2 ^ 2 * 𝔣 4 ^ 2 * 𝔣 8 ^ 4 = 𝔣 4 ^ 12 - 4 * X * 𝔣 2 ^ 4 * 𝔣 8 ^ 8

/-- **A 3-dissection of a quotient of Euler products.** In the ring of integer power series in
$q$, let $f_k = \prod_{m \ge 1} (1 - q^{km})$ denote the Euler products. Then
$f_1^2 f_6 f_9 f_{18} = f_2 f_6 f_9^3 - 2q f_2 f_3 f_{18}^3$. Since every $f_k$ with $k \ge 1$ has
constant term $1$, this is the 3-dissection
$f_1^2 / f_2 = f_9^2 / f_{18} - 2q f_3 f_{18}^2 / (f_6 f_9)$ with denominators cleared.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Lemma 3, (11)
(`integers-2025-A69-lem-3`). -/
public theorem_wanted qEulerProduct_sq_div_three_dissection :
    𝔣 1 ^ 2 * 𝔣 6 * 𝔣 9 * 𝔣 18 = 𝔣 2 * 𝔣 6 * 𝔣 9 ^ 3 - 2 * X * 𝔣 2 * 𝔣 3 * 𝔣 18 ^ 3

/-- **Congruences modulo 32 for $\mathrm{ped}_{9,9}$.** For $k \ge 1$ let
$f_k = \prod_{m \ge 1} (1 - q^{km})$, an integer power series in $q$, and let
$\mathrm{ped}_{9,9}(n)$ be the coefficient of $q^n$ in $f_4 f_{18} / (f_1 f_9)$. Then for all
natural numbers $\alpha$, $\beta$ and $n$ the following congruences modulo $32$ hold, where
every division is exact.

(18) The coefficient of $q^n$ in
$f_2^2 \sum_{m \ge 0} \mathrm{ped}_{9,9}(3^{4\alpha+2} m + (3^{4\alpha+2} - 1)/2) q^m$ is congruent
to the coefficient of $q^n$ in $4 f_1^3 f_3 f_4 f_6 + 16 q f_2^2 f_6^6$. This is the source's
congruence $\sum_{m \ge 0} \mathrm{ped}_{9,9}(3^{4\alpha+2} m + (3^{4\alpha+2} - 1)/2) q^m \equiv
4 f_1^3 f_3 f_4 f_6 / f_2^2 + 16 q f_6^6$ multiplied by $f_2^2$.

(19) $\mathrm{ped}_{9,9}(4 \cdot 3^{4\alpha+6} n + (19 \cdot 3^{4\alpha+5} - 1)/2) \equiv
\mathrm{ped}_{9,9}(4 \cdot 3^{4\alpha+4} n + (19 \cdot 3^{4\alpha+3} - 1)/2)$.

(20) $\mathrm{ped}_{9,9}(4 \cdot 3^{4\alpha+4} \cdot 5^{2\beta} n +
(19 \cdot 3^{4\alpha+3} \cdot 5^{2\beta} - 1)/2)$ is congruent to the coefficient of $q^n$ in
$16 f_1 f_6^3$.

(21) $\mathrm{ped}_{9,9}(4 \cdot 3^{4\alpha+4} \cdot 5^{2\beta+1} (5n + i) +
(23 \cdot 3^{4\alpha+3} \cdot 5^{2\beta+1} - 1)/2) \equiv 0$ for $i \in \{0, 1, 2, 4\}$.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Theorem 1 (`integers-2025-A69-thm-1`). -/
public theorem_wanted pedNineNine_congruences_mod_thirtyTwo (α β n : ℕ) :
    coeff n (𝔣 2 ^ 2 *
        PowerSeries.mk fun m => pedNineNine (3 ^ (4 * α + 2) * m + (3 ^ (4 * α + 2) - 1) / 2)) ≡
      coeff n (4 * 𝔣 1 ^ 3 * 𝔣 3 * 𝔣 4 * 𝔣 6 + 16 * X * 𝔣 2 ^ 2 * 𝔣 6 ^ 6) [ZMOD 32] ∧
    pedNineNine (4 * 3 ^ (4 * α + 6) * n + (19 * 3 ^ (4 * α + 5) - 1) / 2) ≡
      pedNineNine (4 * 3 ^ (4 * α + 4) * n + (19 * 3 ^ (4 * α + 3) - 1) / 2) [ZMOD 32] ∧
    pedNineNine (4 * 3 ^ (4 * α + 4) * 5 ^ (2 * β) * n + (19 * 3 ^ (4 * α + 3) * 5 ^ (2 * β) - 1) / 2)
      ≡ coeff n (16 * 𝔣 1 * 𝔣 6 ^ 3) [ZMOD 32] ∧
    ∀ i ∈ ({0, 1, 2, 4} : Finset ℕ),
      pedNineNine (4 * 3 ^ (4 * α + 4) * 5 ^ (2 * β + 1) * (5 * n + i) +
        (23 * 3 ^ (4 * α + 3) * 5 ^ (2 * β + 1) - 1) / 2) ≡ 0 [ZMOD 32]

/-- **Congruences modulo 16 for $\mathrm{ped}_{9,9}$.** For $k \ge 1$ let
$f_k = \prod_{m \ge 1} (1 - q^{km})$, an integer power series in $q$, and let
$\mathrm{ped}_{9,9}(n)$ be the coefficient of $q^n$ in $f_4 f_{18} / (f_1 f_9)$. Then for all
natural numbers $\alpha$, $\beta$, $\gamma$ and $n$ the following congruences modulo $16$ hold,
where every division is exact.

(49) $\mathrm{ped}_{9,9}(4 \cdot 3^{4\alpha+6} n + (13 \cdot 3^{4\alpha+5} - 1)/2) \equiv 0$ and
$\mathrm{ped}_{9,9}(4 \cdot 3^{4\alpha+4} n + (13 \cdot 3^{4\alpha+3} - 1)/2) \equiv 0$.

(50) $\mathrm{ped}_{9,9}(4 \cdot 3^{4\alpha+6} n + (7 \cdot 3^{4\alpha+5} - 1)/2) \equiv
\mathrm{ped}_{9,9}(4 \cdot 3^{4\alpha+4} n + (7 \cdot 3^{4\alpha+3} - 1)/2)$.

(51) $\mathrm{ped}_{9,9}(2 \cdot 3^{4\alpha+5} n + (11 \cdot 3^{4\alpha+4} - 1)/2) \equiv 0$ and
$\mathrm{ped}_{9,9}(2 \cdot 3^{4\alpha+3} n + (11 \cdot 3^{4\alpha+2} - 1)/2) \equiv 0$.

(52) $\mathrm{ped}_{9,9}(2 \cdot 3^{4\alpha+6} n + (11 \cdot 3^{4\alpha+5} - 1)/2) \equiv 0$ and
$\mathrm{ped}_{9,9}(2 \cdot 3^{4\alpha+4} n + (11 \cdot 3^{4\alpha+3} - 1)/2) \equiv 0$.

(53) $\mathrm{ped}_{9,9}(4 \cdot 3^{4\alpha+4} \cdot 5^{2\beta} n +
(7 \cdot 3^{4\alpha+3} \cdot 5^{2\beta} - 1)/2)$ is congruent to the coefficient of $q^n$ in
$8 f_1^7$.

(54) $\mathrm{ped}_{9,9}(4 \cdot 3^{4\alpha+4} \cdot 5^{2\beta+1} (5n + i) +
(11 \cdot 3^{4\alpha+3} \cdot 5^{2\beta+1} - 1)/2) \equiv 0$ for $i \in \{0, 2, 3, 4\}$.

(55) $\mathrm{ped}_{9,9}(4 \cdot 3^{4\alpha+3} \cdot 7^{2\gamma} n +
(5 \cdot 3^{4\alpha+2} \cdot 7^{2\gamma} - 1)/2)$ is congruent to the coefficient of $q^n$ in
$8 f_1^5$.

(56) $\mathrm{ped}_{9,9}(4 \cdot 3^{4\alpha+3} \cdot 7^{2\gamma+1} (7n + j) +
(11 \cdot 3^{4\alpha+2} \cdot 7^{2\gamma+1} - 1)/2) \equiv 0$ for $j \in \{0, 2, 3, 4, 5, 6\}$.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Theorem 2 (`integers-2025-A69-thm-2`). -/
public theorem_wanted pedNineNine_congruences_mod_sixteen (α β γ n : ℕ) :
    pedNineNine (4 * 3 ^ (4 * α + 6) * n + (13 * 3 ^ (4 * α + 5) - 1) / 2) ≡ 0 [ZMOD 16] ∧
    pedNineNine (4 * 3 ^ (4 * α + 4) * n + (13 * 3 ^ (4 * α + 3) - 1) / 2) ≡ 0 [ZMOD 16] ∧
    pedNineNine (4 * 3 ^ (4 * α + 6) * n + (7 * 3 ^ (4 * α + 5) - 1) / 2) ≡
      pedNineNine (4 * 3 ^ (4 * α + 4) * n + (7 * 3 ^ (4 * α + 3) - 1) / 2) [ZMOD 16] ∧
    pedNineNine (2 * 3 ^ (4 * α + 5) * n + (11 * 3 ^ (4 * α + 4) - 1) / 2) ≡ 0 [ZMOD 16] ∧
    pedNineNine (2 * 3 ^ (4 * α + 3) * n + (11 * 3 ^ (4 * α + 2) - 1) / 2) ≡ 0 [ZMOD 16] ∧
    pedNineNine (2 * 3 ^ (4 * α + 6) * n + (11 * 3 ^ (4 * α + 5) - 1) / 2) ≡ 0 [ZMOD 16] ∧
    pedNineNine (2 * 3 ^ (4 * α + 4) * n + (11 * 3 ^ (4 * α + 3) - 1) / 2) ≡ 0 [ZMOD 16] ∧
    pedNineNine (4 * 3 ^ (4 * α + 4) * 5 ^ (2 * β) * n + (7 * 3 ^ (4 * α + 3) * 5 ^ (2 * β) - 1) / 2)
      ≡ coeff n (8 * 𝔣 1 ^ 7) [ZMOD 16] ∧
    (∀ i ∈ ({0, 2, 3, 4} : Finset ℕ),
      pedNineNine (4 * 3 ^ (4 * α + 4) * 5 ^ (2 * β + 1) * (5 * n + i) +
        (11 * 3 ^ (4 * α + 3) * 5 ^ (2 * β + 1) - 1) / 2) ≡ 0 [ZMOD 16]) ∧
    pedNineNine (4 * 3 ^ (4 * α + 3) * 7 ^ (2 * γ) * n + (5 * 3 ^ (4 * α + 2) * 7 ^ (2 * γ) - 1) / 2)
      ≡ coeff n (8 * 𝔣 1 ^ 5) [ZMOD 16] ∧
    ∀ j ∈ ({0, 2, 3, 4, 5, 6} : Finset ℕ),
      pedNineNine (4 * 3 ^ (4 * α + 3) * 7 ^ (2 * γ + 1) * (7 * n + j) +
        (11 * 3 ^ (4 * α + 2) * 7 ^ (2 * γ + 1) - 1) / 2) ≡ 0 [ZMOD 16]

/-- **Further congruences modulo 16 for $\mathrm{ped}_{9,9}$.** For $k \ge 1$ let
$f_k = \prod_{m \ge 1} (1 - q^{km})$, an integer power series in $q$, and let
$\mathrm{ped}_{9,9}(n)$ be the coefficient of $q^n$ in $f_4 f_{18} / (f_1 f_9)$. Then for all
natural numbers $\alpha$, $\beta$, $\gamma$ and $n$ the following congruences modulo $16$ hold,
where every division is exact.

(58) $\mathrm{ped}_{9,9}(4 \cdot 3^{4\alpha+3} n + (13 \cdot 3^{4\alpha+2} - 1)/2) \equiv 0$.

(59) $\mathrm{ped}_{9,9}(4 \cdot 3^{4\alpha+3} n + (19 \cdot 3^{4\alpha+2} - 1)/2) \equiv 0$.

(60) $\mathrm{ped}_{9,9}(4 \cdot 3^{4\alpha+3} \cdot 5^{2\beta} n +
(7 \cdot 3^{4\alpha+2} \cdot 5^{2\beta} - 1)/2)$ is congruent to the coefficient of $q^n$ in
$8 f_1^7$.

(61) $\mathrm{ped}_{9,9}(4 \cdot 3^{4\alpha+3} \cdot 5^{2\beta+1} (5n + i) +
(11 \cdot 3^{4\alpha+2} \cdot 5^{2\beta+1} - 1)/2) \equiv 0$ for $i \in \{0, 2, 3, 4\}$.

(62) $\mathrm{ped}_{9,9}(4 \cdot 3^{4\alpha+5} n + (13 \cdot 3^{4\alpha+4} - 1)/2) \equiv 0$.

(63) $\mathrm{ped}_{9,9}(2 \cdot 3^{4\alpha+5} n + (7 \cdot 3^{4\alpha+4} - 1)/2) \equiv
\mathrm{ped}_{9,9}(2 \cdot 3^{4\alpha+3} n + (7 \cdot 3^{4\alpha+2} - 1)/2)$.

(64) $\mathrm{ped}_{9,9}(4 \cdot 3^{4\alpha+4} \cdot 7^{2\gamma} n +
(5 \cdot 3^{4\alpha+3} \cdot 7^{2\gamma} - 1)/2)$ is congruent to the coefficient of $q^n$ in
$8 f_1^5$.

(65) $\mathrm{ped}_{9,9}(4 \cdot 3^{4\alpha+4} \cdot 7^{2\gamma+1} (7n + j) +
(11 \cdot 3^{4\alpha+3} \cdot 7^{2\gamma+1} - 1)/2) \equiv 0$ for $j \in \{0, 2, 3, 4, 5, 6\}$.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Theorem 3 (`integers-2025-A69-thm-3`). -/
public theorem_wanted pedNineNine_more_congruences_mod_sixteen (α β γ n : ℕ) :
    pedNineNine (4 * 3 ^ (4 * α + 3) * n + (13 * 3 ^ (4 * α + 2) - 1) / 2) ≡ 0 [ZMOD 16] ∧
    pedNineNine (4 * 3 ^ (4 * α + 3) * n + (19 * 3 ^ (4 * α + 2) - 1) / 2) ≡ 0 [ZMOD 16] ∧
    pedNineNine (4 * 3 ^ (4 * α + 3) * 5 ^ (2 * β) * n + (7 * 3 ^ (4 * α + 2) * 5 ^ (2 * β) - 1) / 2)
      ≡ coeff n (8 * 𝔣 1 ^ 7) [ZMOD 16] ∧
    (∀ i ∈ ({0, 2, 3, 4} : Finset ℕ),
      pedNineNine (4 * 3 ^ (4 * α + 3) * 5 ^ (2 * β + 1) * (5 * n + i) +
        (11 * 3 ^ (4 * α + 2) * 5 ^ (2 * β + 1) - 1) / 2) ≡ 0 [ZMOD 16]) ∧
    pedNineNine (4 * 3 ^ (4 * α + 5) * n + (13 * 3 ^ (4 * α + 4) - 1) / 2) ≡ 0 [ZMOD 16] ∧
    pedNineNine (2 * 3 ^ (4 * α + 5) * n + (7 * 3 ^ (4 * α + 4) - 1) / 2) ≡
      pedNineNine (2 * 3 ^ (4 * α + 3) * n + (7 * 3 ^ (4 * α + 2) - 1) / 2) [ZMOD 16] ∧
    pedNineNine (4 * 3 ^ (4 * α + 4) * 7 ^ (2 * γ) * n + (5 * 3 ^ (4 * α + 3) * 7 ^ (2 * γ) - 1) / 2)
      ≡ coeff n (8 * 𝔣 1 ^ 5) [ZMOD 16] ∧
    ∀ j ∈ ({0, 2, 3, 4, 5, 6} : Finset ℕ),
      pedNineNine (4 * 3 ^ (4 * α + 4) * 7 ^ (2 * γ + 1) * (7 * n + j) +
        (11 * 3 ^ (4 * α + 3) * 7 ^ (2 * γ + 1) - 1) / 2) ≡ 0 [ZMOD 16]

/-- **Congruences modulo 64 for [9, 18]-overpartitions with even parts distinct.** Let
$\mathrm{ped}_{9,18}(n)$ be the number of $[9, 18]$-overpartitions of $n$ with even parts
distinct, let $f_k = \prod_{m \ge 1} (1 - q^{km})$, and read congruences between integer power
series in $q$ coefficientwise. For all $\alpha \ge 0$ the following hold modulo $64$, where the
statements about single values hold for every $n \ge 0$:
(73) $f_2^2 \sum_{n \ge 0} \mathrm{ped}_{9,18}\bigl(3^{4\alpha+2} n + (3^{4\alpha+3} + 1)/4\bigr)
q^n \equiv 12 f_1^4 f_3^6$;
(74) $\mathrm{ped}_{9,18}\bigl(3^{4\alpha+5} n + (7 \cdot 3^{4\alpha+4} + 1)/4\bigr) \equiv
\mathrm{ped}_{9,18}\bigl(3^{4\alpha+3} n + (7 \cdot 3^{4\alpha+2} + 1)/4\bigr)$;
(75) $\mathrm{ped}_{9,18}\bigl(3^{4\alpha+5} n + (11 \cdot 3^{4\alpha+4} + 1)/4\bigr) \equiv
\mathrm{ped}_{9,18}\bigl(3^{4\alpha+3} n + (11 \cdot 3^{4\alpha+2} + 1)/4\bigr)$;
(76) $\mathrm{ped}_{9,18}\bigl(3^{4\alpha+6} n + (5 \cdot 3^{4\alpha+5} + 1)/4\bigr) \equiv
\mathrm{ped}_{9,18}\bigl(3^{4\alpha+4} n + (5 \cdot 3^{4\alpha+3} + 1)/4\bigr)$.
All divisions by $4$ are exact.

The paper states (73) with $12 f_1^4 f_3^6 / f_2^2$ on the right; here $f_2^2$ is cleared.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Theorem 4 (`integers-2025-A69-thm-4`). -/
public theorem_wanted pedNineEighteen_congruences_mod_sixtyFour (α n : ℕ) :
    coeff n (𝔣 2 ^ 2 *
        PowerSeries.mk fun m => pedNineEighteen (3 ^ (4 * α + 2) * m + (3 ^ (4 * α + 3) + 1) / 4)) ≡
      coeff n (12 * 𝔣 1 ^ 4 * 𝔣 3 ^ 6) [ZMOD 64] ∧
    pedNineEighteen (3 ^ (4 * α + 5) * n + (7 * 3 ^ (4 * α + 4) + 1) / 4) ≡
      pedNineEighteen (3 ^ (4 * α + 3) * n + (7 * 3 ^ (4 * α + 2) + 1) / 4) [ZMOD 64] ∧
    pedNineEighteen (3 ^ (4 * α + 5) * n + (11 * 3 ^ (4 * α + 4) + 1) / 4) ≡
      pedNineEighteen (3 ^ (4 * α + 3) * n + (11 * 3 ^ (4 * α + 2) + 1) / 4) [ZMOD 64] ∧
    pedNineEighteen (3 ^ (4 * α + 6) * n + (5 * 3 ^ (4 * α + 5) + 1) / 4) ≡
      pedNineEighteen (3 ^ (4 * α + 4) * n + (5 * 3 ^ (4 * α + 3) + 1) / 4) [ZMOD 64]

/-- **Congruences modulo 32 for [9, 18]-overpartitions with even parts distinct.** Let
$\mathrm{ped}_{9,18}(n)$ be the number of $[9, 18]$-overpartitions of $n$ with even parts
distinct, let $f_k = \prod_{m \ge 1} (1 - q^{km})$, and read congruences between integer power
series in $q$ coefficientwise. For all $\alpha, \beta \ge 0$ the following hold modulo $32$, where
the statements about single values hold for every $n \ge 0$:
(94) $\mathrm{ped}_{9,18}\bigl(3^{4\alpha+6} n + (3^{4\alpha+5} + 1)/4\bigr) \equiv
\mathrm{ped}_{9,18}\bigl(3^{4\alpha+4} n + (3^{4\alpha+3} + 1)/4\bigr)$;
(95) $\sum_{n \ge 0} \mathrm{ped}_{9,18}\bigl(2 \cdot 3^{4\alpha+3} 5^{2\beta} n +
(7 \cdot 3^{4\alpha+2} 5^{2\beta} + 1)/4\bigr) q^n \equiv 16 f_1^7$;
(96) $\mathrm{ped}_{9,18}\bigl(2 \cdot 3^{4\alpha+3} 5^{2\beta+1} (5n + i) +
(11 \cdot 3^{4\alpha+2} 5^{2\beta+1} + 1)/4\bigr) \equiv 0$ for $i \in \{0, 2, 3, 4\}$;
(97) $\sum_{n \ge 0} \mathrm{ped}_{9,18}\bigl(2 \cdot 3^{4\alpha+3} 5^{2\beta} n +
(19 \cdot 3^{4\alpha+2} 5^{2\beta} + 1)/4\bigr) q^n \equiv 16 f_1 f_6^3$;
(98) $\mathrm{ped}_{9,18}\bigl(2 \cdot 3^{4\alpha+3} 5^{2\beta+1} (5n + j) +
(23 \cdot 3^{4\alpha+2} 5^{2\beta+1} + 1)/4\bigr) \equiv 0$ for $j \in \{0, 1, 2, 4\}$;
(99) $\mathrm{ped}_{9,18}\bigl(2 \cdot 3^{4\alpha+3} n + (23 \cdot 3^{4\alpha+2} + 1)/4\bigr)
\equiv 0$;
(100) $\sum_{n \ge 0} \mathrm{ped}_{9,18}\bigl(2 \cdot 3^{4\alpha+3} 5^{2\beta} n +
(11 \cdot 3^{4\alpha+2} 5^{2\beta} + 1)/4\bigr) q^n \equiv 16 f_2 f_3^3$;
(101) $\mathrm{ped}_{9,18}\bigl(2 \cdot 3^{4\alpha+3} 5^{2\beta+1} (5n + k) +
(7 \cdot 3^{4\alpha+2} 5^{2\beta+1} + 1)/4\bigr) \equiv 0$ for $k \in \{0, 1, 3, 4\}$.
All divisions by $4$ are exact.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Theorem 5 (`integers-2025-A69-thm-5`). -/
public theorem_wanted pedNineEighteen_congruences_mod_thirtyTwo (α β n : ℕ) :
    pedNineEighteen (3 ^ (4 * α + 6) * n + (3 ^ (4 * α + 5) + 1) / 4) ≡
      pedNineEighteen (3 ^ (4 * α + 4) * n + (3 ^ (4 * α + 3) + 1) / 4) [ZMOD 32] ∧
    pedNineEighteen
        (2 * 3 ^ (4 * α + 3) * 5 ^ (2 * β) * n + (7 * 3 ^ (4 * α + 2) * 5 ^ (2 * β) + 1) / 4)
      ≡ coeff n (16 * 𝔣 1 ^ 7) [ZMOD 32] ∧
    (∀ i ∈ ({0, 2, 3, 4} : Finset ℕ),
      pedNineEighteen (2 * 3 ^ (4 * α + 3) * 5 ^ (2 * β + 1) * (5 * n + i) +
        (11 * 3 ^ (4 * α + 2) * 5 ^ (2 * β + 1) + 1) / 4) ≡ 0 [ZMOD 32]) ∧
    pedNineEighteen
        (2 * 3 ^ (4 * α + 3) * 5 ^ (2 * β) * n + (19 * 3 ^ (4 * α + 2) * 5 ^ (2 * β) + 1) / 4)
      ≡ coeff n (16 * 𝔣 1 * 𝔣 6 ^ 3) [ZMOD 32] ∧
    (∀ j ∈ ({0, 1, 2, 4} : Finset ℕ),
      pedNineEighteen (2 * 3 ^ (4 * α + 3) * 5 ^ (2 * β + 1) * (5 * n + j) +
        (23 * 3 ^ (4 * α + 2) * 5 ^ (2 * β + 1) + 1) / 4) ≡ 0 [ZMOD 32]) ∧
    pedNineEighteen (2 * 3 ^ (4 * α + 3) * n + (23 * 3 ^ (4 * α + 2) + 1) / 4) ≡ 0 [ZMOD 32] ∧
    pedNineEighteen
        (2 * 3 ^ (4 * α + 3) * 5 ^ (2 * β) * n + (11 * 3 ^ (4 * α + 2) * 5 ^ (2 * β) + 1) / 4)
      ≡ coeff n (16 * 𝔣 2 * 𝔣 3 ^ 3) [ZMOD 32] ∧
    ∀ k ∈ ({0, 1, 3, 4} : Finset ℕ),
      pedNineEighteen (2 * 3 ^ (4 * α + 3) * 5 ^ (2 * β + 1) * (5 * n + k) +
        (7 * 3 ^ (4 * α + 2) * 5 ^ (2 * β + 1) + 1) / 4) ≡ 0 [ZMOD 32]

/-- **Congruences modulo 16 and 8 for [9, 18]-overpartitions with even parts distinct.** Let
$\mathrm{ped}_{9,18}(n)$ be the number of $[9, 18]$-overpartitions of $n$ with even parts
distinct, let $f_k = \prod_{m \ge 1} (1 - q^{km})$, and read congruences between integer power
series in $q$ coefficientwise. For all $\alpha, \beta, \gamma \ge 0$ the following hold, where the
statements about single values hold for every $n \ge 0$:
(105) $\sum_{n \ge 0} \mathrm{ped}_{9,18}\bigl(2 \cdot 3^{4\alpha+4} 5^{2\beta} n +
(13 \cdot 3^{4\alpha+3} 5^{2\beta} + 1)/4\bigr) q^n \equiv 8 f_1^{13} \pmod{16}$;
(106) $\mathrm{ped}_{9,18}\bigl(2 \cdot 3^{4\alpha+4} 5^{2\beta+1} (5n + i) +
(17 \cdot 3^{4\alpha+3} 5^{2\beta+1} + 1)/4\bigr) \equiv 0 \pmod{16}$ for $i \in \{0, 1, 3, 4\}$;
(107) $\sum_{n \ge 0} \mathrm{ped}_{9,18}\bigl(2 \cdot 3^{4\alpha+4} 7^{2\gamma} n +
(5 \cdot 3^{4\alpha+3} 7^{2\gamma} + 1)/4\bigr) q^n \equiv 8 f_1^5 \pmod{16}$;
(108) $\mathrm{ped}_{9,18}\bigl(2 \cdot 3^{4\alpha+4} 7^{2\gamma+1} (7n + j) +
(11 \cdot 3^{4\alpha+3} 7^{2\gamma+1} + 1)/4\bigr) \equiv 0 \pmod{16}$ for
$j \in \{0, 2, 3, 4, 5, 6\}$;
(109) $\mathrm{ped}_{9,18}\bigl(2 \cdot 3^{4\alpha+4} n + (3^{4\alpha+3} + 1)/4\bigr)$ is congruent
to $4$ modulo $8$ if $n = m(3m-1)/2$ for some integer $m$ (a generalized pentagonal number), and
to $0$ modulo $8$ otherwise.
All divisions by $4$ are exact.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Theorem 6 (`integers-2025-A69-thm-6`). -/
public theorem_wanted pedNineEighteen_congruences_mod_sixteen (α β γ n : ℕ) :
    pedNineEighteen
        (2 * 3 ^ (4 * α + 4) * 5 ^ (2 * β) * n + (13 * 3 ^ (4 * α + 3) * 5 ^ (2 * β) + 1) / 4)
      ≡ coeff n (8 * 𝔣 1 ^ 13) [ZMOD 16] ∧
    (∀ i ∈ ({0, 1, 3, 4} : Finset ℕ),
      pedNineEighteen (2 * 3 ^ (4 * α + 4) * 5 ^ (2 * β + 1) * (5 * n + i) +
        (17 * 3 ^ (4 * α + 3) * 5 ^ (2 * β + 1) + 1) / 4) ≡ 0 [ZMOD 16]) ∧
    pedNineEighteen
        (2 * 3 ^ (4 * α + 4) * 7 ^ (2 * γ) * n + (5 * 3 ^ (4 * α + 3) * 7 ^ (2 * γ) + 1) / 4)
      ≡ coeff n (8 * 𝔣 1 ^ 5) [ZMOD 16] ∧
    (∀ j ∈ ({0, 2, 3, 4, 5, 6} : Finset ℕ),
      pedNineEighteen (2 * 3 ^ (4 * α + 4) * 7 ^ (2 * γ + 1) * (7 * n + j) +
        (11 * 3 ^ (4 * α + 3) * 7 ^ (2 * γ + 1) + 1) / 4) ≡ 0 [ZMOD 16]) ∧
    ((∃ m : ℤ, 2 * (n : ℤ) = m * (3 * m - 1)) →
      pedNineEighteen (2 * 3 ^ (4 * α + 4) * n + (3 ^ (4 * α + 3) + 1) / 4) ≡ 4 [ZMOD 8]) ∧
    ((¬ ∃ m : ℤ, 2 * (n : ℤ) = m * (3 * m - 1)) →
      pedNineEighteen (2 * 3 ^ (4 * α + 4) * n + (3 ^ (4 * α + 3) + 1) / 4) ≡ 0 [ZMOD 8])

/-- **Congruences modulo 9 and 27 for [9, 18]-overpartitions with even parts distinct.** Let
$\mathrm{ped}_{9,18}(n)$ be the number of $[9, 18]$-overpartitions of $n$ with even parts
distinct. For every $n \ge 0$, $\mathrm{ped}_{9,18}(27n + 16)$ and $\mathrm{ped}_{9,18}(27n + 25)$
are divisible by $9$, and $\mathrm{ped}_{9,18}(243n + 142)$, $\mathrm{ped}_{9,18}(243n + 223)$ and
$\mathrm{ped}_{9,18}(729n + 547)$ are divisible by $27$.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Theorem 7 (`integers-2025-A69-thm-7`). -/
public theorem_wanted pedNineEighteen_congruences_mod_nine_twentySeven (n : ℕ) :
    pedNineEighteen (27 * n + 16) ≡ 0 [ZMOD 9] ∧ pedNineEighteen (27 * n + 25) ≡ 0 [ZMOD 9] ∧
      pedNineEighteen (243 * n + 142) ≡ 0 [ZMOD 27] ∧
      pedNineEighteen (243 * n + 223) ≡ 0 [ZMOD 27] ∧
      pedNineEighteen (729 * n + 547) ≡ 0 [ZMOD 27]

/-- **Congruences modulo 27 for [9, 18]-overpartitions from the cubic coefficient vectors.** Let
$\mathrm{ped}_{9,18}(n)$ be the number of $[9, 18]$-overpartitions of $n$ with even parts
distinct, let $f_k = \prod_{m \ge 1} (1 - q^{km})$, let
$X_\alpha = (x_{\alpha,1}, x_{\alpha,2}, \dots)$ be the coefficient vectors built from Chan's
matrix, and read congruences between integer power series in $q$ coefficientwise. For all
$\alpha \ge 0$, modulo $27$,
(124) $\sum_{n \ge 0} \mathrm{ped}_{9,18}\bigl(3^{2\alpha+5} n + (3^{2\alpha+5} + 1)/4\bigr) q^n
\equiv 9 \sum_{i=1}^{3^{2\alpha}} x_{2\alpha,i} \, q^{i-1}
\left(\frac{f_3 f_6}{f_1 f_2}\right)^{4i-3}$ and
(125) $\sum_{n \ge 0} \mathrm{ped}_{9,18}\bigl(3^{2\alpha+6} n + (3^{2\alpha+7} + 1)/4\bigr) q^n
\equiv 9 \sum_{i=1}^{3^{2\alpha+1}} x_{2\alpha+1,i} \, q^{i-1}
\left(\frac{f_3 f_6}{f_1 f_2}\right)^{4i-1}$.
All divisions by $4$ are exact, and $f_1 f_2$ is invertible as a power series because its
constant term is $1$.

The quotient $f_3 f_6 / (f_1 f_2)$ is the generating function of 3-regular cubic partitions.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Theorem 8 (`integers-2025-A69-thm-8`). -/
public theorem_wanted pedNineEighteen_cubicCoeffVector_congruences (α n : ℕ) :
    pedNineEighteen (3 ^ (2 * α + 5) * n + (3 ^ (2 * α + 5) + 1) / 4) ≡
      coeff n (9 * ∑ i ∈ Finset.range (3 ^ (2 * α)), (cubicCoeffVector (2 * α) i : ℤ⟦X⟧) *
        X ^ i * (𝔣 3 * 𝔣 6) ^ (4 * i + 1) * invOfUnit ((𝔣 1 * 𝔣 2) ^ (4 * i + 1)) 1) [ZMOD 27] ∧
    pedNineEighteen (3 ^ (2 * α + 6) * n + (3 ^ (2 * α + 7) + 1) / 4) ≡
      coeff n (9 * ∑ i ∈ Finset.range (3 ^ (2 * α + 1)),
        (cubicCoeffVector (2 * α + 1) i : ℤ⟦X⟧) * X ^ i * (𝔣 3 * 𝔣 6) ^ (4 * i + 3) *
          invOfUnit ((𝔣 1 * 𝔣 2) ^ (4 * i + 3)) 1) [ZMOD 27]

end

end MetaMathlibExt
