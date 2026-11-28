/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import MathlibExt.NumberTheory.EisensteinRamanujanCongruence

open PowerSeries
open scoped PowerSeries.WithPiTopology

-- At weight 12 the weight-zero factor is 1, giving the Ramanujan congruence modulo 691.
example (n : ℕ) (hn : 1 ≤ n) :
    let Δ : ℚ⟦X⟧ := X * ∏' j : ℕ, (1 - X ^ (j + 1)) ^ 24
    (((ArithmeticFunction.sigma 11 n : ℚ) - coeff n Δ) / 691).den.Coprime 691 := by
  intro Δ
  have h := (MetaMathlibExt.eisenstein_congr_delta_mul_eisenstein_dim_one 12 (by decide)).2 n hn
  have hB : (-bernoulli 12 / (2 * 12)).num.natAbs = 691 := by decide +kernel
  have hunit : PowerSeries.mk (fun j => if j = 0 then (1 : ℚ) else 0) = 1 := by
    ext j
    simp [coeff_one]
  simpa [show n ≠ 0 by omega, hunit, hB, Nat.sup_divisors_id, Δ] using h

-- At k = 24 and n = 0 the congruence compares the Bernoulli constant term.
-- (k is let-bound so that the filter predicate in N' elaborates.)
example :
    let k := 24
    let σ₀ : ℕ → ℕ → ℚ := fun w n => if w = 0 then (if n = 0 then 1 else 0)
      else if n = 0 then -bernoulli w / (2 * w) else (ArithmeticFunction.sigma (w - 1) n : ℚ)
    let Δ : ℚ⟦X⟧ := X * ∏' j : ℕ, (1 - X ^ (j + 1)) ^ 24
    let b : ℕ → ℕ → ℚ := fun i n =>
      coeff n (Δ ^ i * PowerSeries.mk (σ₀ (k - 12 * i))) / σ₀ (k - 12 * i) 0
    let Nw : ℕ → ℕ := fun w => if w ≤ 2 then 1 else (σ₀ w 0).num.natAbs
    let N' : ℕ := ((Nat.divisors (Nw k)).filter fun d =>
      ∀ i ∈ Finset.Icc 1 (k / 12), Nat.Coprime d (Nw (k - 12 * i))).sup id
    let γ₂ : ℚ := 2 ^ (k - 1) + 25 - 1 / σ₀ (k - 12) 0
    ((σ₀ k 0 - (b 1 0 + γ₂ * b 2 0)) / N').den.Coprime N' := by
  intro k σ₀ Δ b Nw N' γ₂
  exact (MetaMathlibExt.eisenstein_congr_delta_mul_eisenstein_dim_two 24 (by decide)).1 0

-- At k = 24 and n = 5 the congruence compares a divisor sum at a non-degenerate index.
example :
    let k := 24
    let σ₀ : ℕ → ℕ → ℚ := fun w n => if w = 0 then (if n = 0 then 1 else 0)
      else if n = 0 then -bernoulli w / (2 * w) else (ArithmeticFunction.sigma (w - 1) n : ℚ)
    let Δ : ℚ⟦X⟧ := X * ∏' j : ℕ, (1 - X ^ (j + 1)) ^ 24
    let b : ℕ → ℕ → ℚ := fun i n =>
      coeff n (Δ ^ i * PowerSeries.mk (σ₀ (k - 12 * i))) / σ₀ (k - 12 * i) 0
    let Nw : ℕ → ℕ := fun w => if w ≤ 2 then 1 else (σ₀ w 0).num.natAbs
    let N' : ℕ := ((Nat.divisors (Nw k)).filter fun d =>
      ∀ i ∈ Finset.Icc 1 (k / 12), Nat.Coprime d (Nw (k - 12 * i))).sup id
    let γ₂ : ℚ := 2 ^ (k - 1) + 25 - 1 / σ₀ (k - 12) 0
    ((σ₀ k 5 - (b 1 5 + γ₂ * b 2 5)) / N').den.Coprime N' := by
  intro k σ₀ Δ b Nw N' γ₂
  exact (MetaMathlibExt.eisenstein_congr_delta_mul_eisenstein_dim_two 24 (by decide)).2 5
    (by decide)

-- At k = 38 and n = 0 the modulus filters over three weights.
example :
    let k := 38
    let σ₀ : ℕ → ℕ → ℚ := fun w n => if w = 0 then (if n = 0 then 1 else 0)
      else if n = 0 then -bernoulli w / (2 * w) else (ArithmeticFunction.sigma (w - 1) n : ℚ)
    let Δ : ℚ⟦X⟧ := X * ∏' j : ℕ, (1 - X ^ (j + 1)) ^ 24
    let b : ℕ → ℕ → ℚ := fun i n =>
      coeff n (Δ ^ i * PowerSeries.mk (σ₀ (k - 12 * i))) / σ₀ (k - 12 * i) 0
    let Nw : ℕ → ℕ := fun w => if w ≤ 2 then 1 else (σ₀ w 0).num.natAbs
    let N' : ℕ := ((Nat.divisors (Nw k)).filter fun d =>
      ∀ i ∈ Finset.Icc 1 (k / 12), Nat.Coprime d (Nw (k - 12 * i))).sup id
    let γ₂ : ℚ := 2 ^ (k - 1) + 25 - 1 / σ₀ (k - 12) 0
    ((σ₀ k 0 - (b 1 0 + γ₂ * b 2 0)) / N').den.Coprime N' := by
  intro k σ₀ Δ b Nw N' γ₂
  exact (MetaMathlibExt.eisenstein_congr_delta_mul_eisenstein_dim_two 38 (by decide)).1 0

-- At k = 38 and n = 7 the congruence compares a divisor sum with inner weight 14.
example :
    let k := 38
    let σ₀ : ℕ → ℕ → ℚ := fun w n => if w = 0 then (if n = 0 then 1 else 0)
      else if n = 0 then -bernoulli w / (2 * w) else (ArithmeticFunction.sigma (w - 1) n : ℚ)
    let Δ : ℚ⟦X⟧ := X * ∏' j : ℕ, (1 - X ^ (j + 1)) ^ 24
    let b : ℕ → ℕ → ℚ := fun i n =>
      coeff n (Δ ^ i * PowerSeries.mk (σ₀ (k - 12 * i))) / σ₀ (k - 12 * i) 0
    let Nw : ℕ → ℕ := fun w => if w ≤ 2 then 1 else (σ₀ w 0).num.natAbs
    let N' : ℕ := ((Nat.divisors (Nw k)).filter fun d =>
      ∀ i ∈ Finset.Icc 1 (k / 12), Nat.Coprime d (Nw (k - 12 * i))).sup id
    let γ₂ : ℚ := 2 ^ (k - 1) + 25 - 1 / σ₀ (k - 12) 0
    ((σ₀ k 7 - (b 1 7 + γ₂ * b 2 7)) / N').den.Coprime N' := by
  intro k σ₀ Δ b Nw N' γ₂
  exact (MetaMathlibExt.eisenstein_congr_delta_mul_eisenstein_dim_two 38 (by decide)).1 7

private def sigma₀ (w n : ℕ) : ℚ :=
  if w = 0 then (if n = 0 then 1 else 0)
  else if n = 0 then -bernoulli w / (2 * w) else (ArithmeticFunction.sigma (w - 1) n : ℚ)

private noncomputable def delta : ℚ⟦X⟧ := X * ∏' j : ℕ, (1 - X ^ (j + 1)) ^ 24

private noncomputable def b (k i n : ℕ) : ℚ :=
  coeff n (delta ^ i * PowerSeries.mk (sigma₀ (k - 12 * i))) / sigma₀ (k - 12 * i) 0

private def modulus (k : ℕ) : ℕ :=
  let Nw (w : ℕ) := if w ≤ 2 then 1 else (sigma₀ w 0).num.natAbs
  ((Nat.divisors (Nw k)).filter fun d =>
    ∀ i ∈ Finset.Icc 1 (k / 12), Nat.Coprime d (Nw (k - 12 * i))).sup id

private def gamma₂ (k : ℕ) : ℚ := 2 ^ (k - 1) + 25 - 1 / sigma₀ (k - 12) 0

private def gamma₃ (k : ℕ) : ℚ :=
  3 ^ (k - 1) + 2 ^ (k - 1) * 48 + 949 - (2 ^ (k - 13) + 25) / sigma₀ (k - 12) 0 -
    (2 ^ (k - 1) + 25) / sigma₀ (k - 24) 0 + 1 / (sigma₀ (k - 12) 0 * sigma₀ (k - 24) 0)

-- At the weight-zero endpoint the third basis element is just Δ³, even at n = 0.
example (n : ℕ) :
    ((sigma₀ 36 n - (b 36 1 n + gamma₂ 36 * b 36 2 n + gamma₃ 36 * coeff n (delta ^ 3))) /
      modulus 36).den.Coprime (modulus 36) := by
  have h := (MetaMathlibExt.eisenstein_congr_delta_mul_eisenstein_dim_three 36 (by decide)).1 n
  change ((sigma₀ 36 n - (b 36 1 n + gamma₂ 36 * b 36 2 n + gamma₃ 36 * b 36 3 n)) /
    modulus 36).den.Coprime (modulus 36) at h
  have hunit : PowerSeries.mk (sigma₀ 0) = 1 := by
    ext j
    simp [sigma₀, coeff_one]
  rwa [show b 36 3 n = coeff n (delta ^ 3) by
    change coeff n (delta ^ 3 * PowerSeries.mk (sigma₀ 0)) / sigma₀ 0 0 = _
    simp [hunit, show sigma₀ 0 0 = 1 by decide]] at h

-- The weight-50 case reaches the weight-14 endpoint. Use a coefficient beyond the three
-- coefficients that determined γ₂ and γ₃.
example :
    ((sigma₀ 50 4 - (b 50 1 4 + gamma₂ 50 * b 50 2 4 + gamma₃ 50 * b 50 3 4)) /
      modulus 50).den.Coprime (modulus 50) :=
  (MetaMathlibExt.eisenstein_congr_delta_mul_eisenstein_dim_three 50 (by decide)).2 4 (by decide)

private noncomputable def matrixSumAt (k m n : ℕ) : ℚ :=
  let C : Matrix (Fin m) (Fin m) ℚ := fun i j => b k (i.val + 1) (j.val + 1)
  let γ : Fin m → ℚ := Matrix.vecMul (fun j => sigma₀ k (j.val + 1)) C⁻¹
  ∑ i : Fin m, γ i * b k (i.val + 1) n

private noncomputable def matrixSum (k n : ℕ) : ℚ :=
  matrixSumAt k (if k % 12 = 2 then k / 12 - 1 else k / 12) n

private lemma b_first_coeffs (k : ℕ) (h : sigma₀ (k - 12) 0 ≠ 0) :
    b k 1 1 = 1 ∧ b k 1 2 = sigma₀ (k - 12) 1 / sigma₀ (k - 12) 0 - 24 := by
  let P := pentagonalSeries ℚ
  have hp₀ : constantCoeff P = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply,
      show (0 : ℕ) = pentagonal 0 by norm_num [pentagonal_def]]
    simp [P, coeff_pentagonalSeries_pentagonal]
  have hp₁ : coeff 1 P = -1 := by
    rw [show (1 : ℕ) = pentagonal 1 by norm_num [pentagonal_def]]
    norm_num [P, coeff_pentagonalSeries_pentagonal]
  have hP : constantCoeff (P ^ 24) = 1 := by simp [hp₀]
  have hP₁ : coeff 1 (P ^ 24) = -24 := by
    rw [coeff_one_pow, hp₀, hp₁]
    norm_num
  have hΔ : delta = X * P ^ 24 := by
    rw [delta, ← ((WithPiTopology.hasProd_one_sub_X_pow ℚ).pow 24).tprod_eq]
  simp only [b, pow_one, mul_one, hΔ, mul_assoc]
  constructor
  · rw [show (1 : ℕ) = 0 + 1 by decide, coeff_succ_X_mul,
      coeff_zero_eq_constantCoeff_apply, map_mul, hP, one_mul, constantCoeff_mk, div_self h]
  · rw [show (2 : ℕ) = 1 + 1 by decide, coeff_succ_X_mul, coeff_one_mul, hP, hP₁,
      mul_one, coeff_mk, constantCoeff_mk]
    field_simp
    ring

private lemma matrixSum_of_dim_one (k n : ℕ) (hk : k ≠ 0)
    (hm : (if k % 12 = 2 then k / 12 - 1 else k / 12) = 1)
    (h : sigma₀ (k - 12) 0 ≠ 0) : matrixSum k n = b k 1 n := by
  rw [matrixSum, hm]
  let C : Matrix (Fin 1) (Fin 1) ℚ := fun i j => b k (i.val + 1) (j.val + 1)
  have hC : C = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simpa [C] using (b_first_coeffs k h).1
  change (∑ i : Fin 1, Matrix.vecMul (fun j => sigma₀ k (j.val + 1)) C⁻¹ i *
    b k (i.val + 1) n) = b k 1 n
  rw [hC, Matrix.inv_def, Matrix.det_one, Ring.inverse_one, one_smul, Matrix.adjugate_one,
    Matrix.vecMul_one]
  simp [sigma₀, hk]

private lemma modulus_eq_of_inner_one (k : ℕ)
    (h : ∀ i ∈ Finset.Icc 1 (k / 12),
      (if k - 12 * i ≤ 2 then 1 else (sigma₀ (k - 12 * i) 0).num.natAbs) = 1) :
    modulus k = (if k ≤ 2 then 1 else (sigma₀ k 0).num.natAbs) := by
  unfold modulus
  dsimp only
  rw [Finset.filter_eq_self.mpr (fun d _ i hi => by rw [h i hi]; simp), Nat.sup_divisors_id]

-- For k = 12 the inner weight is zero, and the q² difference is exactly 3 · 691.
example : modulus 12 = 691 ∧ (sigma₀ 12 2 - matrixSum 12 2) / modulus 12 = 3 := by
  have hN : modulus 12 = 691 := by
    rw [modulus_eq_of_inner_one 12 (by
      intro i hi
      simp only [Finset.mem_Icc] at hi
      have : i = 1 := by omega
      subst i
      decide)]
    decide +kernel
  refine ⟨hN, ?_⟩
  rw [matrixSum_of_dim_one 12 2 (by decide) (by decide) (by decide),
    (b_first_coeffs 12 (by decide)).2, hN]
  decide +kernel

-- At k = 26 the modulus filter keeps the full numerator, while the matrix omits weight two.
-- The q² difference is computed without reducing the large Bernoulli numerator at weight 26.
example : modulus 26 = (sigma₀ 26 0).num.natAbs ∧ sigma₀ 26 2 - matrixSum 26 2 = 33554481 := by
  have h14 : sigma₀ 14 0 = -1 / 24 := by decide +kernel
  have h0 : sigma₀ (26 - 12) 0 ≠ 0 := by
    change sigma₀ 14 0 ≠ 0
    rw [h14]
    norm_num
  constructor
  · rw [modulus_eq_of_inner_one 26 (by
      intro i hi
      simp only [Finset.mem_Icc] at hi
      have : i = 1 ∨ i = 2 := by omega
      rcases this with rfl | rfl
      · change (sigma₀ 14 0).num.natAbs = 1
        rw [h14]
        decide +kernel
      · decide)]
    rfl
  · rw [matrixSum_of_dim_one 26 2 (by decide) (by decide) h0, (b_first_coeffs 26 h0).2]
    change sigma₀ 26 2 - (sigma₀ 14 1 / sigma₀ 14 0 - 24) = 33554481
    rw [h14]
    decide +kernel

-- Also check that the public declaration uses these same matrix and modulus conventions.
example : ((sigma₀ 26 2 - matrixSum 26 2) / modulus 26).den.Coprime (modulus 26) :=
  MetaMathlibExt.eisenstein_congr_sum_delta_pow_mul_eisenstein 26 (by decide) (by decide)
    (by decide) 2
