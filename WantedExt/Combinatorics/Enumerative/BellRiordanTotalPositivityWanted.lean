/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Analysis.Real.Sqrt
public import MathlibExt.Combinatorics.Enumerative.BellRiordanTotalPositivity
public import MathlibExt.LinearAlgebra.Matrix.LowerToeplitz
public import MathlibExt.LinearAlgebra.Matrix.NonnegativeMinors

/-!
# Total positivity of Bell-type Riordan arrays

Statement from Lili Mu, Yuanyuan Xing and Sai-Nan Zheng, *A New Criterion for the Total
Positivity of Riordan Arrays*, Journal of Integer Sequences 28 (2025), Article 25.7.5.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **A total positivity criterion for Riordan arrays.** Let $P, Q, A, Z$ be formal power series
over $\mathbb{R}$ with $P(0) \ne 0$, write $[x^n]F$ for the coefficient of $x^n$ in a power
series $F$, and let $a, b, r, s, t \ge 0$ be real numbers. Suppose that
$$A(x)\,(P(x) - rx) = P(x)^2 + sxP(x) + tx^2$$
and
$$Z(x)\,(P(x)^2 - rxP(x)) =
(P(x)^2 + sxP(x) + tx^2)\,Q(x) + (aP(x) + bx)(P(x) - xQ(x)),$$
and let $R$ be the Riordan array whose $A$-sequence is $([x^n]A)_{n \ge 0}$ and whose
$Z$-sequence is $([x^n]Z)_{n \ge 0}$. Let $J(Q(x), P(x))$ be the coefficient matrix whose row
$n \ge 0$ reads $[x^n]Q, [x^n]P, [x^{n-1}]P, \dots, [x^0]P, 0, 0, \dots$. Call a matrix totally
positive when every minor of it is nonnegative. If $J(Q(x), P(x))$ is totally positive,
$s^2 \ge 4t$ and $as + a\sqrt{s^2 - 4t} \ge 2b$, then $R$ is totally positive.

Since $P(0) \ne 0$, the series $P(x) - rx$ and $P(x)^2 - rxP(x)$ are invertible, so the two
hypotheses say $A = (P^2 + sxP + tx^2)/(P - rx)$ and
$Z = ((P^2 + sxP + tx^2)Q + (aP + bx)(P - xQ))/(P^2 - rxP)$.

Source: Lili Mu, Yuanyuan Xing and Sai-Nan Zheng, *A New Criterion for the Total Positivity of
Riordan Arrays*, Journal of Integer Sequences 28 (2025), Article 25.7.5, Theorem 2
(`jis-2025-25.7.5-thm-2`). -/
public theorem_wanted riordanArray_hasNonnegativeMinors_of_params (P Q A Z : PowerSeries ℝ)
    (hP : PowerSeries.constantCoeff P ≠ 0) {a b r s t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hA : A * (P - PowerSeries.C r * PowerSeries.X) =
      P ^ 2 + PowerSeries.C s * PowerSeries.X * P + PowerSeries.C t * PowerSeries.X ^ 2)
    (hZ : Z * (P ^ 2 - PowerSeries.C r * PowerSeries.X * P) =
      (P ^ 2 + PowerSeries.C s * PowerSeries.X * P + PowerSeries.C t * PowerSeries.X ^ 2) * Q +
        (PowerSeries.C a * P + PowerSeries.C b * PowerSeries.X) * (P - PowerSeries.X * Q))
    {R : ℕ → ℕ → ℝ}
    (hR : IsRiordanArrayAZ (fun n => PowerSeries.coeff n A) (fun n => PowerSeries.coeff n Z) R)
    (hJ : Matrix.HasNonnegativeMinors
      (riordanCoeffMatrix (fun n => PowerSeries.coeff n Q) (fun n => PowerSeries.coeff n P)))
    (hst : 4 * t ≤ s ^ 2) (hab : 2 * b ≤ a * s + a * Real.sqrt (s ^ 2 - 4 * t)) :
    Matrix.HasNonnegativeMinors (Matrix.of R)

/-- **Total positivity of Bell-type Riordan arrays from a Pólya frequency series.** Let $P$ and
$A$ be formal power series over $\mathbb{R}$ with $P(0) \ne 0$, write $[x^n]F$ for the
coefficient of $x^n$ in a power series $F$, and let $r, s, t \ge 0$ be real numbers with
$s^2 \ge 4t$. Suppose that $P$ is a Pólya frequency series, that is, every minor of the lower
Toeplitz matrix of its coefficients (whose entry in row $n$ and column $k$ is $[x^{n-k}]P$ for
$k \le n$ and $0$ otherwise) is nonnegative, and that
$$A(x)\,(P(x) - rx) = P(x)^2 + sxP(x) + tx^2.$$
Let $R$ be the Riordan array with $A$-sequence $(a_n)_{n \ge 0}$ and $Z$-sequence
$(z_n)_{n \ge 0}$, where $a_n = [x^n]A$ and $z_n = a_{n+1}$ (a Bell-type Riordan array). Then
$R$ is totally positive: every minor of $R$ is nonnegative.

Since $P(0) \ne 0$, the series $P(x) - rx$ is invertible, so the hypothesis on $A$ says
$A = (P^2 + sxP + tx^2)/(P - rx)$.

Source: Lili Mu, Yuanyuan Xing and Sai-Nan Zheng, *A New Criterion for the Total Positivity of
Riordan Arrays*, Journal of Integer Sequences 28 (2025), Article 25.7.5, Corollary 6
(`jis-2025-25.7.5-cor-6`). -/
public theorem_wanted bellRiordanArray_hasNonnegativeMinors_of_pf (P A : PowerSeries ℝ)
    (hP : PowerSeries.constantCoeff P ≠ 0) {r s t : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hpf : Matrix.HasNonnegativeMinors (Matrix.lowerToeplitz fun n => PowerSeries.coeff n P))
    (hA : A * (P - PowerSeries.C r * PowerSeries.X) =
      P ^ 2 + PowerSeries.C s * PowerSeries.X * P + PowerSeries.C t * PowerSeries.X ^ 2)
    {R : ℕ → ℕ → ℝ}
    (hR : IsRiordanArrayAZ (fun n => PowerSeries.coeff n A)
      (fun n => PowerSeries.coeff (n + 1) A) R)
    (hst : 4 * t ≤ s ^ 2) :
    Matrix.HasNonnegativeMinors (Matrix.of R)

end

end MetaMathlibExt
