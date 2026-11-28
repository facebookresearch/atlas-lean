/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.LinearAlgebra.Matrix.Notation
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

private def weightNumerator (w : ℕ) : ℕ :=
  if w ≤ 2 then 1 else (sigma₀ w 0).num.natAbs

private def eligibleDivisors (k : ℕ) : Finset ℕ :=
  (Nat.divisors (weightNumerator k)).filter fun d =>
    ∀ i ∈ Finset.Icc 1 (k / 12), Nat.Coprime d (weightNumerator (k - 12 * i))

private def modulus (k : ℕ) : ℕ := (eligibleDivisors k).sup id

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

private lemma delta_eq_X_mul : delta = X * pentagonalSeries ℚ ^ 24 := by
  rw [delta, ← ((WithPiTopology.hasProd_one_sub_X_pow ℚ).pow 24).tprod_eq]

private lemma b_first_coeffs (k : ℕ) (h : sigma₀ (k - 12) 0 ≠ 0) :
    b k 1 1 = 1 ∧ b k 1 2 = sigma₀ (k - 12) 1 / sigma₀ (k - 12) 0 - 24 := by
  have hP := MetaMathlibExt.constantCoeff_pentagonalSeries_pow ℚ 24
  have hP₁ : coeff 1 (pentagonalSeries ℚ ^ 24) = -24 :=
    MetaMathlibExt.coeff_one_pentagonalSeries_pow ℚ 24
  simp only [b, pow_one, mul_one, delta_eq_X_mul, mul_assoc]
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
    (h : ∀ i ∈ Finset.Icc 1 (k / 12), weightNumerator (k - 12 * i) = 1) :
    modulus k = weightNumerator k := by
  unfold modulus eligibleDivisors
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

-- Cache smaller values as a list so that the kernel can check large Bernoulli numerators
-- without repeatedly evaluating the same subproblems of the defining recurrence.
private def bernoulliPrefix : ℕ → List ℚ
  | 0 => []
  | n + 1 =>
    let bs := bernoulliPrefix n
    bs ++ [1 - ∑ k ∈ Finset.range n, (n.choose k : ℚ) / (n - k + 1) * (bs[k]?).getD 0]

private lemma length_bernoulliPrefix (n : ℕ) : (bernoulliPrefix n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bernoulliPrefix, ih]

private lemma getD_bernoulliPrefix (n j : ℕ) (hj : j < n) :
    ((bernoulliPrefix n)[j]?).getD 0 = bernoulli' j := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    rw [bernoulliPrefix]
    by_cases h : j < n
    · rw [List.getElem?_append_left (by simpa only [length_bernoulliPrefix] using h)]
      exact ih j h
    · have he : j = n := by omega
      subst j
      rw [List.getElem?_append_right (by rw [length_bernoulliPrefix]),
        length_bernoulliPrefix, Nat.sub_self, bernoulli'_def]
      simp only [List.getElem?_cons_zero, Option.getD_some]
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [ih k (Finset.mem_range.mp hk)]

private lemma weightNumerator_eq_prefix (k : ℕ) (hk : 2 < k) :
    weightNumerator k = (-((bernoulliPrefix (k + 1))[k]?).getD 0 / (2 * k)).num.natAbs := by
  simp [weightNumerator, not_le.mpr hk, sigma₀, show k ≠ 0 by omega,
    getD_bernoulliPrefix _ _ (Nat.lt_succ_self _),
    bernoulli_eq_bernoulli'_of_ne_one (by omega : k ≠ 1)]

-- At k = 24 the off-diagonal entry is nonzero, and the q³ difference is 400 times the modulus.
set_option maxRecDepth 4096 in
private lemma weight24_arithmetic :
    let C : Matrix (Fin 2) (Fin 2) ℚ := fun i j => b 24 (i.val + 1) (j.val + 1)
    C ≠ 1 ∧ modulus 24 = 236364091 ∧ (sigma₀ 24 3 - matrixSum 24 3) / modulus 24 = 400 := by
  intro C
  have hE : sigma₀ 12 0 = 691 / 65520 := by decide +kernel
  have hE₁ : sigma₀ 12 1 = 1 := by decide +kernel
  have hE₂ : sigma₀ 12 2 = 2049 := by decide +kernel
  have h0 : sigma₀ (24 - 12) 0 ≠ 0 := by
    change sigma₀ 12 0 ≠ 0
    rw [hE]
    norm_num
  obtain ⟨hb₁₁, hb₁₂⟩ := b_first_coeffs 24 h0
  have hb₁₂' : b 24 1 2 = 48936 / 691 := by
    rw [hb₁₂]
    change sigma₀ 12 1 / sigma₀ 12 0 - 24 = _
    rw [hE, hE₁]
    norm_num
  have hb₁₃ : b 24 1 3 = 132852132 / 691 := by
    simp only [b, pow_one, Nat.mul_one, delta_eq_X_mul, mul_assoc,
      show (24 : ℕ) - 12 = 12 by decide]
    have h : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by decide
    rw [show (3 : ℕ) = 2 + 1 by decide, coeff_succ_X_mul, coeff_mul, h]
    norm_num [coeff_zero_eq_constantCoeff_apply, MetaMathlibExt.constantCoeff_pentagonalSeries_pow,
      MetaMathlibExt.coeff_one_pentagonalSeries_pow, MetaMathlibExt.coeff_two_pentagonalSeries_pow,
      show (24 : ℕ).choose 2 = 276 by decide, hE, hE₁, hE₂]
  have hunit : PowerSeries.mk (sigma₀ 0) = (1 : ℚ⟦X⟧) := by
    ext j
    simp [sigma₀, coeff_one]
  have hb₂ (j : ℕ) : b 24 2 j = coeff j ((X : ℚ⟦X⟧) ^ 2 * (pentagonalSeries ℚ ^ 24) ^ 2) := by
    simp only [b, show (24 : ℕ) - 12 * 2 = 0 by decide, hunit, mul_one,
      show sigma₀ 0 0 = 1 by decide, div_one, delta_eq_X_mul, mul_pow]
  have hP := MetaMathlibExt.constantCoeff_pentagonalSeries_pow ℚ 24
  have hb₂₁ : b 24 2 1 = 0 := by rw [hb₂, coeff_X_pow_mul']; norm_num
  have hb₂₂ : b 24 2 2 = 1 := by
    rw [hb₂, coeff_X_pow_mul']
    norm_num [coeff_zero_eq_constantCoeff_apply, hP]
  have hb₂₃ : b 24 2 3 = -48 := by
    rw [hb₂, coeff_X_pow_mul']
    norm_num [← pow_mul, MetaMathlibExt.coeff_one_pentagonalSeries_pow]
  have hC : C = !![1, 48936 / 691; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [C, hb₁₁, hb₁₂', hb₂₁, hb₂₂]
  have hne : C ≠ 1 := by
    intro hh
    have := congrFun (congrFun (hC.symm.trans hh) 0) 1
    norm_num [Matrix.one_fin_two] at this
  have hM : modulus 24 = 236364091 := by
    have hN : weightNumerator 24 = 236364091 := by
      rw [weightNumerator_eq_prefix 24 (by decide)]
      decide +kernel
    unfold modulus eligibleDivisors
    rw [hN, Finset.filter_eq_self.mpr ?_, Nat.sup_divisors_id]
    intro d hd i hi
    simp only [Finset.mem_Icc] at hi
    have hi' : i = 1 ∨ i = 2 := by omega
    rcases hi' with rfl | rfl
    · have hcop : (236364091 : ℕ).Coprime (weightNumerator 12) := by
        change (236364091 : ℕ).Coprime (sigma₀ 12 0).num.natAbs
        rw [hE]
        decide +kernel
      exact hcop.of_dvd_left (Nat.dvd_of_mem_divisors hd)
    · exact Nat.coprime_one_right _
  refine ⟨hne, hM, ?_⟩
  rw [hM]
  let D : Matrix (Fin 2) (Fin 2) ℚ := !![1, -(48936 / 691); 0, 1]
  have hInv : C⁻¹ = D := by
    apply Matrix.inv_eq_left_inv
    rw [hC]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [D, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_fin_two]
  change (sigma₀ 24 3 - ∑ i : Fin 2,
    Matrix.vecMul (fun j => sigma₀ 24 (j.val + 1)) C⁻¹ i * b 24 (i.val + 1) 3) / 236364091 = 400
  rw [hInv]
  simp only [Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two]
  norm_num [D, hb₁₃, hb₂₃, show sigma₀ 24 1 = 1 by decide +kernel,
    show sigma₀ 24 2 = 8388609 by decide +kernel, show sigma₀ 24 3 = 94143178828 by decide +kernel]

-- Check the same weight-24 value in the convolution form, and pin the corollary's API.
example :
    let conv (i n : ℕ) := coeff n (delta ^ i * PowerSeries.mk (sigma₀ (24 - 12 * i)))
    let C : Matrix (Fin 2) (Fin 2) ℚ := fun i j => b 24 (i.val + 1) (j.val + 1)
    let γ := Matrix.vecMul (fun j : Fin 2 => sigma₀ 24 (j.val + 1)) C⁻¹
    let q := (sigma₀ 24 3 - ∑ i : Fin 2,
      γ i / sigma₀ (24 - 12 * (i.val + 1)) 0 * conv (i.val + 1) 3) / modulus 24
    q = 400 ∧ q.den.Coprime (modulus 24) := by
  intro conv C γ q
  refine ⟨?_, MetaMathlibExt.sigma_congr_sum_tau_conv_sigma 24 (by decide) (by decide)
    (by decide) 3 (by decide)⟩
  have h := weight24_arithmetic.2.2
  change (sigma₀ 24 3 - ∑ i : Fin 2,
    γ i * (conv (i.val + 1) 3 / sigma₀ (24 - 12 * (i.val + 1)) 0)) / modulus 24 = 400 at h
  simpa only [q, ← mul_div_assoc, div_mul_eq_mul_div] using h

-- The lower weight 32 shares the prime 37 with weight 68; the modulus drops that factor.
set_option maxRecDepth 4096 in
example : 37 ∣ weightNumerator 68 ∧ 37 ∣ weightNumerator 32 ∧ ¬ 37 ∣ modulus 68 := by
  have h68 : weightNumerator 68 = 4633713579924631067171126424027918014373353 := by
    rw [weightNumerator_eq_prefix 68 (by decide)]
    decide +kernel
  have h32 : 37 ∣ weightNumerator 32 := by
    rw [weightNumerator_eq_prefix 32 (by decide)]
    decide +kernel
  refine ⟨?_, h32, ?_⟩
  · rw [h68]
    decide
  · have hs : (eligibleDivisors 68).Nonempty := ⟨1, by simp [eligibleDivisors, h68]⟩
    obtain ⟨d, hd, heq⟩ := Finset.sup_mem_of_nonempty (f := id) hs
    change d = modulus 68 at heq
    have hdmod : modulus 68 ∈ eligibleDivisors 68 := heq ▸ hd
    unfold eligibleDivisors at hdmod
    have hcop : (modulus 68).Coprime (weightNumerator 32) :=
      (Finset.mem_filter.mp hdmod).2 3 (by decide)
    exact fun h => (by decide : ¬ Nat.Coprime 37 37) ((hcop.of_dvd_left h).of_dvd_right h32)

-- These clients use the same one-term matrix and modulus as the independent checks above.
example : ((sigma₀ 12 2 - matrixSumAt 12 1 2) / modulus 12).den.Coprime (modulus 12) :=
  MetaMathlibExt.eisenstein_congr_sum_delta_pow_mul_eisenstein 12 (by decide) (by decide)
    (by decide) 2

example : ((sigma₀ 26 2 - matrixSumAt 26 1 2) / modulus 26).den.Coprime (modulus 26) :=
  MetaMathlibExt.eisenstein_congr_sum_delta_pow_mul_eisenstein 26 (by decide) (by decide)
    (by decide) 2

-- Match the public statement before specializing n: simplifying at n = 0 would hide the matrix.
-- Check both the constant term and a coefficient of degree greater than m.
example :
    ((sigma₀ 24 0 - matrixSumAt 24 2 0) / modulus 24).den.Coprime (modulus 24) ∧
    ((sigma₀ 24 3 - matrixSumAt 24 2 3) / modulus 24).den.Coprime (modulus 24) := by
  have h (n : ℕ) :
      ((sigma₀ 24 n - matrixSumAt 24 2 n) / modulus 24).den.Coprime (modulus 24) :=
    MetaMathlibExt.eisenstein_congr_sum_delta_pow_mul_eisenstein 24 (by decide) (by decide)
      (by decide) n
  exact ⟨h 0, h 3⟩

example :
    ((sigma₀ 68 0 - matrixSumAt 68 5 0) / modulus 68).den.Coprime (modulus 68) ∧
    ((sigma₀ 68 6 - matrixSumAt 68 5 6) / modulus 68).den.Coprime (modulus 68) := by
  have h (n : ℕ) :
      ((sigma₀ 68 n - matrixSumAt 68 5 n) / modulus 68).den.Coprime (modulus 68) :=
    MetaMathlibExt.eisenstein_congr_sum_delta_pow_mul_eisenstein 68 (by decide) (by decide)
      (by decide) n
  exact ⟨h 0, h 6⟩
