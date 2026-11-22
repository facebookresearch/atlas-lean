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

/-- Ramanujan's 5-dissection of Euler's product:
`f_1 = f_{25} (R(q^5)⁻¹ - q - q^2 R(q^5))` with `R(q) = f(-q, -q^4) / f(-q^2, -q^3)`, for
complex `‖q‖ < 1`.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Lemma 5 (`integers-2025-A69-lem-5`). -/
public theorem_wanted qPochhammerInf_five_dissection (q : ℂ) (hq : ‖q‖ < 1) :
    let R : ℂ → ℂ := fun x => ramanujanThetaRaw (-x) (-x ^ 4) / ramanujanThetaRaw (-x ^ 2) (-x ^ 3)
    qPochhammerInfRaw q q =
      qPochhammerInfRaw (q ^ 25) (q ^ 25) * ((R (q ^ 5))⁻¹ - q - q ^ 2 * R (q ^ 5))

/-- Ramanujan's 7-dissection of Euler's product:
`f_1 = f_{49} (B(q^7)/C(q^7) - q A(q^7)/B(q^7) - q^2 + q^5 C(q^7)/A(q^7))` with
`A(q) = f(-q^3, -q^4)`, `B(q) = f(-q^2, -q^5)`, `C(q) = f(-q, -q^6)`, for complex `‖q‖ < 1`.

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

/-- The generating function `∑ ped_{9,9}(n) q^n = f_4 f_18 / (f_1 f_9)` of `[9, 9]`-overpartitions
with even parts distinct, as an integer power series.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, equations (2) and (22). -/
noncomputable def pedNineNineSeries : ℤ⟦X⟧ :=
  𝔣 4 * 𝔣 18 * invOfUnit (𝔣 1 * 𝔣 9) 1

/-- `ped_{9,9}(n)`, the number of `[9, 9]`-overpartitions of `n` with even parts distinct, defined
as the `n`th coefficient of `f_4 f_18 / (f_1 f_9)`.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, equations (2) and (22). -/
noncomputable def pedNineNine (n : ℕ) : ℤ :=
  coeff n pedNineNineSeries

/-- The generating function `∑ ped_{9,18}(n) q^n = f_4 f_18^2 / (f_1 f_9 f_36)` of
`[9, 18]`-overpartitions with even parts distinct, as an integer power series.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, equations (2) and (77). -/
noncomputable def pedNineEighteenSeries : ℤ⟦X⟧ :=
  𝔣 4 * 𝔣 18 ^ 2 * invOfUnit (𝔣 1 * 𝔣 9 * 𝔣 36) 1

/-- `ped_{9,18}(n)`, the number of `[9, 18]`-overpartitions of `n` with even parts distinct,
defined as the `n`th coefficient of `f_4 f_18^2 / (f_1 f_9 f_36)`.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, equations (2) and (77). -/
noncomputable def pedNineEighteen (n : ℕ) : ℤ :=
  coeff n pedNineEighteenSeries

/-- The defining identity `f_1 f_9 ∑ ped_{9,9}(n) q^n = f_4 f_18`.

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

/-- The defining identity `f_1 f_9 f_36 ∑ ped_{9,18}(n) q^n = f_4 f_18^2`.

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

/-- `ped_{9,9}(0) = ped_{9,18}(0) = 1` (the empty overpartition).

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

/-- Chan's matrix `(m_{i,j})`: `m_{1,1} = 3`, `m_{2,1} = 2`, `m_{3,1} = 1`, `m_{i,1} = 0` for
`i ≥ 4`, and `m_{i,j} = 9 m_{i-1,j-1} + 3 m_{i-2,j-1} + m_{i-3,j-1}` for `j ≥ 2`, with entries of
row index `≤ 0` equal to `0`. Here `chanCubicMatrix i j = m_{i,j}` for `i, j ≥ 1`; row `0` and
column `0` are `0`, and natural subtraction sends the out-of-range rows `i - 1, i - 2, i - 3 < 1`
to row `0`.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Section 2 (from H. C. Chan, Int. J. Number
Theory 6 (2010), (11)-(19)). -/
def chanCubicMatrix : ℕ → ℕ → ℤ
  | _, 0 => 0
  | i, 1 => if i = 1 then 3 else if i = 2 then 2 else if i = 3 then 1 else 0
  | i, j + 2 =>
      9 * chanCubicMatrix (i - 1) (j + 1) + 3 * chanCubicMatrix (i - 2) (j + 1) +
        chanCubicMatrix (i - 3) (j + 1)

/-- The first six rows of Chan's matrix as printed in the paper:
`(3)`, `(2, 27)`, `(1, 27, 243)`, `(0, 18, 324, 2187)`, `(0, 5, 270, 3645, 19683)`,
`(0, 1, 126, 3645, 39366, 177147)`.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Section 2. -/
theorem chanCubicMatrix_first_rows :
    (List.range 6).map (fun i => (List.range 6).map fun j => chanCubicMatrix (i + 1) (j + 1)) =
      [[3, 0, 0, 0, 0, 0], [2, 27, 0, 0, 0, 0], [1, 27, 243, 0, 0, 0],
        [0, 18, 324, 2187, 0, 0], [0, 5, 270, 3645, 19683, 0],
        [0, 1, 126, 3645, 39366, 177147]] := by
  decide

/-- The coefficient vectors `X_α = (x_{α,1}, x_{α,2}, …)`: `X_0 = (1, 0, 0, …)` and
`X_{α+1} = X_α A` for even `α`, `X_{α+1} = X_α B` for odd `α`, where `a_{i,j} = m_{4i-3,i+j-1}`
and `b_{i,j} = m_{4i-1,i+j-1}` (`m = chanCubicMatrix`). Indices are shifted to start at `0`:
`cubicCoeffVector α i = x_{α,i+1}`, so `a_{i+1,j+1} = m_{4i+1,i+j+1}` and
`b_{i+1,j+1} = m_{4i+3,i+j+1}`. The row sum runs over `i < 3^α`, which covers the support of
`X_α`: row `i + 1` of `A` or `B` vanishes beyond column `3i + 3` (`m` is lower triangular), so by
induction `x_{α,i+1} = 0` for `i ≥ 3^α`.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Section 2, equations (3)-(4), and
Theorem 8. -/
def cubicCoeffVector : ℕ → ℕ → ℤ
  | 0, i => if i = 0 then 1 else 0
  | α + 1, j => ∑ i ∈ Finset.range (3 ^ α), cubicCoeffVector α i *
      (if Even α then chanCubicMatrix (4 * i + 1) (i + j + 1)
        else chanCubicMatrix (4 * i + 3) (i + j + 1))

/-- `X_1 = (3, 0, 0, …)` and `X_2 = (3, 81, 729, 0, …)` (first five entries).

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Theorem 8. -/
theorem cubicCoeffVector_one_two :
    (List.range 5).map (cubicCoeffVector 1) = [3, 0, 0, 0, 0] ∧
      (List.range 5).map (cubicCoeffVector 2) = [3, 81, 729, 0, 0] := by
  decide

/-- The 2-dissection `f_1^4 = f_4^10 / (f_2^2 f_8^4) - 4q f_2^2 f_8^4 / f_4^2`, stated with
denominators cleared. The paper's companion (6) is the existing `f1_sq_two_dissection`.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Lemma 1, (7)
(`integers-2025-A69-lem-1`). -/
public theorem_wanted qEulerProduct_fourth_two_dissection :
    𝔣 1 ^ 4 * 𝔣 2 ^ 2 * 𝔣 4 ^ 2 * 𝔣 8 ^ 4 = 𝔣 4 ^ 12 - 4 * X * 𝔣 2 ^ 4 * 𝔣 8 ^ 8

/-- The 3-dissection `f_1^2 / f_2 = f_9^2 / f_18 - 2q f_3 f_18^2 / (f_6 f_9)`, stated with
denominators cleared. The paper's companions (10) and (12) are the existing
`f2_sq_div_f1_dissection` and `f2_div_f1_sq_dissection`.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Lemma 3, (11)
(`integers-2025-A69-lem-3`). -/
public theorem_wanted qEulerProduct_sq_div_three_dissection :
    𝔣 1 ^ 2 * 𝔣 6 * 𝔣 9 * 𝔣 18 = 𝔣 2 * 𝔣 6 * 𝔣 9 ^ 3 - 2 * X * 𝔣 2 * 𝔣 3 * 𝔣 18 ^ 3

/-- Congruences modulo `32` for `ped_{9,9}`: for all `n, α, β ≥ 0`,
(18) `∑ ped_{9,9}(3^{4α+2} n + (3^{4α+2} - 1)/2) q^n ≡ 4 f_1^3 f_3 f_4 f_6 / f_2^2 + 16 q f_6^6`
(stated after multiplying both sides by `f_2^2`),
(19) `ped_{9,9}(4·3^{4α+6} n + (19·3^{4α+5} - 1)/2) ≡ ped_{9,9}(4·3^{4α+4} n + (19·3^{4α+3} - 1)/2)`,
(20) `∑ ped_{9,9}(4·3^{4α+4}·5^{2β} n + (19·3^{4α+3}·5^{2β} - 1)/2) q^n ≡ 16 f_1 f_6^3`, and
(21) `ped_{9,9}(4·3^{4α+4}·5^{2β+1}(5n+i) + (23·3^{4α+3}·5^{2β+1} - 1)/2) ≡ 0` for
`i ∈ {0, 1, 2, 4}`. All divisions are exact.

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

/-- Congruences modulo `16` for `ped_{9,9}`: for all `n, α, β, γ ≥ 0`,
(49) `ped_{9,9}(4·3^{4α+6} n + (13·3^{4α+5} - 1)/2) ≡ ped_{9,9}(4·3^{4α+4} n + (13·3^{4α+3} - 1)/2)
≡ 0`,
(50) `ped_{9,9}(4·3^{4α+6} n + (7·3^{4α+5} - 1)/2) ≡ ped_{9,9}(4·3^{4α+4} n + (7·3^{4α+3} - 1)/2)`,
(51) `ped_{9,9}(2·3^{4α+5} n + (11·3^{4α+4} - 1)/2) ≡ ped_{9,9}(2·3^{4α+3} n + (11·3^{4α+2} - 1)/2)
≡ 0`,
(52) `ped_{9,9}(2·3^{4α+6} n + (11·3^{4α+5} - 1)/2) ≡ ped_{9,9}(2·3^{4α+4} n + (11·3^{4α+3} - 1)/2)
≡ 0`,
(53) `∑ ped_{9,9}(4·3^{4α+4}·5^{2β} n + (7·3^{4α+3}·5^{2β} - 1)/2) q^n ≡ 8 f_1^7`,
(54) `ped_{9,9}(4·3^{4α+4}·5^{2β+1}(5n+i) + (11·3^{4α+3}·5^{2β+1} - 1)/2) ≡ 0` for
`i ∈ {0, 2, 3, 4}`,
(55) `∑ ped_{9,9}(4·3^{4α+3}·7^{2γ} n + (5·3^{4α+2}·7^{2γ} - 1)/2) q^n ≡ 8 f_1^5`, and
(56) `ped_{9,9}(4·3^{4α+3}·7^{2γ+1}(7n+j) + (11·3^{4α+2}·7^{2γ+1} - 1)/2) ≡ 0` for
`j ∈ {0, 2, 3, 4, 5, 6}`. All divisions are exact.

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

/-- Further congruences modulo `16` for `ped_{9,9}`: for all `n, α, β, γ ≥ 0`,
(58) `ped_{9,9}(4·3^{4α+3} n + (13·3^{4α+2} - 1)/2) ≡ 0`,
(59) `ped_{9,9}(4·3^{4α+3} n + (19·3^{4α+2} - 1)/2) ≡ 0`,
(60) `∑ ped_{9,9}(4·3^{4α+3}·5^{2β} n + (7·3^{4α+2}·5^{2β} - 1)/2) q^n ≡ 8 f_1^7`,
(61) `ped_{9,9}(4·3^{4α+3}·5^{2β+1}(5n+i) + (11·3^{4α+2}·5^{2β+1} - 1)/2) ≡ 0` for
`i ∈ {0, 2, 3, 4}`,
(62) `ped_{9,9}(4·3^{4α+5} n + (13·3^{4α+4} - 1)/2) ≡ 0`,
(63) `ped_{9,9}(2·3^{4α+5} n + (7·3^{4α+4} - 1)/2) ≡ ped_{9,9}(2·3^{4α+3} n + (7·3^{4α+2} - 1)/2)`,
(64) `∑ ped_{9,9}(4·3^{4α+4}·7^{2γ} n + (5·3^{4α+3}·7^{2γ} - 1)/2) q^n ≡ 8 f_1^5`, and
(65) `ped_{9,9}(4·3^{4α+4}·7^{2γ+1}(7n+j) + (11·3^{4α+3}·7^{2γ+1} - 1)/2) ≡ 0` for
`j ∈ {0, 2, 3, 4, 5, 6}`. All divisions are exact.

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

/-- Congruences modulo `64` for `ped_{9,18}`: for all `n, α ≥ 0`,
(73) `∑ ped_{9,18}(3^{4α+2} n + (3^{4α+3} + 1)/4) q^n ≡ 12 f_1^4 f_3^6 / f_2^2` (stated after
multiplying both sides by `f_2^2`),
(74) `ped_{9,18}(3^{4α+5} n + (7·3^{4α+4} + 1)/4) ≡ ped_{9,18}(3^{4α+3} n + (7·3^{4α+2} + 1)/4)`,
(75) `ped_{9,18}(3^{4α+5} n + (11·3^{4α+4} + 1)/4) ≡ ped_{9,18}(3^{4α+3} n + (11·3^{4α+2} + 1)/4)`,
(76) `ped_{9,18}(3^{4α+6} n + (5·3^{4α+5} + 1)/4) ≡ ped_{9,18}(3^{4α+4} n + (5·3^{4α+3} + 1)/4)`.
All divisions are exact.

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

/-- Congruences modulo `32` for `ped_{9,18}`: for all `n, α, β ≥ 0`,
(94) `ped_{9,18}(3^{4α+6} n + (3^{4α+5} + 1)/4) ≡ ped_{9,18}(3^{4α+4} n + (3^{4α+3} + 1)/4)`,
(95) `∑ ped_{9,18}(2·3^{4α+3}·5^{2β} n + (7·3^{4α+2}·5^{2β} + 1)/4) q^n ≡ 16 f_1^7`,
(96) `ped_{9,18}(2·3^{4α+3}·5^{2β+1}(5n+i) + (11·3^{4α+2}·5^{2β+1} + 1)/4) ≡ 0` for
`i ∈ {0, 2, 3, 4}`,
(97) `∑ ped_{9,18}(2·3^{4α+3}·5^{2β} n + (19·3^{4α+2}·5^{2β} + 1)/4) q^n ≡ 16 f_1 f_6^3`,
(98) `ped_{9,18}(2·3^{4α+3}·5^{2β+1}(5n+j) + (23·3^{4α+2}·5^{2β+1} + 1)/4) ≡ 0` for
`j ∈ {0, 1, 2, 4}`,
(99) `ped_{9,18}(2·3^{4α+3} n + (23·3^{4α+2} + 1)/4) ≡ 0`,
(100) `∑ ped_{9,18}(2·3^{4α+3}·5^{2β} n + (11·3^{4α+2}·5^{2β} + 1)/4) q^n ≡ 16 f_2 f_3^3`, and
(101) `ped_{9,18}(2·3^{4α+3}·5^{2β+1}(5n+k) + (7·3^{4α+2}·5^{2β+1} + 1)/4) ≡ 0` for
`k ∈ {0, 1, 3, 4}`. All divisions are exact.

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

/-- Congruences modulo `16` and `8` for `ped_{9,18}`: for all `n, α, β, γ ≥ 0`,
(105) `∑ ped_{9,18}(2·3^{4α+4}·5^{2β} n + (13·3^{4α+3}·5^{2β} + 1)/4) q^n ≡ 8 f_1^13 (mod 16)`,
(106) `ped_{9,18}(2·3^{4α+4}·5^{2β+1}(5n+i) + (17·3^{4α+3}·5^{2β+1} + 1)/4) ≡ 0 (mod 16)` for
`i ∈ {0, 1, 3, 4}`,
(107) `∑ ped_{9,18}(2·3^{4α+4}·7^{2γ} n + (5·3^{4α+3}·7^{2γ} + 1)/4) q^n ≡ 8 f_1^5 (mod 16)`,
(108) `ped_{9,18}(2·3^{4α+4}·7^{2γ+1}(7n+j) + (11·3^{4α+3}·7^{2γ+1} + 1)/4) ≡ 0 (mod 16)` for
`j ∈ {0, 2, 3, 4, 5, 6}`, and
(109) `ped_{9,18}(2·3^{4α+4} n + (3^{4α+3} + 1)/4)` is `≡ 4 (mod 8)` if `n` is a pentagonal number
and `≡ 0 (mod 8)` otherwise. "Pentagonal number" is read as a generalized pentagonal number
`m(3m-1)/2`, `m ∈ ℤ` (the exponents of `f_1`, which the proof reduces this case to); this is
written `2n = m(3m-1)`. All divisions are exact.

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

/-- Congruences modulo `9` and `27` for `ped_{9,18}`: for all `n ≥ 0`,
`ped_{9,18}(27n + 16) ≡ ped_{9,18}(27n + 25) ≡ 0 (mod 9)` and
`ped_{9,18}(243n + 142) ≡ ped_{9,18}(243n + 223) ≡ ped_{9,18}(729n + 547) ≡ 0 (mod 27)`.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Theorem 7 (`integers-2025-A69-thm-7`). -/
public theorem_wanted pedNineEighteen_congruences_mod_nine_twentySeven (n : ℕ) :
    pedNineEighteen (27 * n + 16) ≡ 0 [ZMOD 9] ∧ pedNineEighteen (27 * n + 25) ≡ 0 [ZMOD 9] ∧
      pedNineEighteen (243 * n + 142) ≡ 0 [ZMOD 27] ∧
      pedNineEighteen (243 * n + 223) ≡ 0 [ZMOD 27] ∧
      pedNineEighteen (729 * n + 547) ≡ 0 [ZMOD 27]

/-- For all `n, α ≥ 0`, modulo `27`,
(124) `∑ ped_{9,18}(3^{2α+5} n + (3^{2α+5} + 1)/4) q^n ≡
9 ∑_{i ≥ 1} x_{2α,i} q^{i-1} (f_3 f_6 / (f_1 f_2))^{4i-3}` and
(125) `∑ ped_{9,18}(3^{2α+6} n + (3^{2α+7} + 1)/4) q^n ≡
9 ∑_{i ≥ 1} x_{2α+1,i} q^{i-1} (f_3 f_6 / (f_1 f_2))^{4i-1}`,
with the coefficient vectors `X_α = (x_{α,i})` of `cubicCoeffVector` (indices shifted to start at
`0`; the sums run over the support `i < 3^α` of `X_α`). The quotient `f_3 f_6 / (f_1 f_2)` is the
generating function of 3-regular cubic partitions; the inverse is `invOfUnit`, the inverse of a
power series with constant coefficient `1`. All divisions of integers are exact.

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
