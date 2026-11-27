/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.QuantumInformation.Finite.QuantumFourierTransform
public import Mathlib.Analysis.Fourier.ZMod

/-!
# The quantum Fourier transform matrix as a discrete Fourier transform

The normalized quantum Fourier transform matrix is `√q` times Mathlib's
inverse discrete Fourier transform on `ZMod q`, and its conjugate transpose
is `(√q)⁻¹` times Mathlib's discrete Fourier transform. For `q = 2 ^ n` the
entries factor over the bits of the row index.

## Source

P. W. Shor, *Polynomial-time algorithms for prime factorization and discrete
logarithms on a quantum computer*, SIAM J. Comput. 26 (1997), 1484–1509,
Section 4, equation (4.1).
-/

@[expose] public section

open Matrix

namespace MathlibExt.QuantumInformation.Finite.QuantumFourierTransform

set_option autoImplicit false

private theorem finEquiv_val (q : ℕ) [NeZero q] (j : Fin q) :
    (ZMod.finEquiv q j).val = j.val := by
  cases q with
  | zero =>
    have h := j.isLt
    omega
  | succ n => rfl

private theorem finEquiv_natCast (q : ℕ) [NeZero q] (j : Fin q) :
    ZMod.finEquiv q j = ((j.val : ℕ) : ZMod q) := by
  rw [← ZMod.natCast_zmod_val (ZMod.finEquiv q j), finEquiv_val q j]

private theorem stdAddChar_finEquiv_mul (q : ℕ) [NeZero q] (j k : Fin q) :
    ZMod.stdAddChar (ZMod.finEquiv q j * ZMod.finEquiv q k)
      = Complex.exp (2 * Real.pi * Complex.I * ((j.val * k.val : ℕ) : ℂ) / q) := by
  rw [finEquiv_natCast q j, finEquiv_natCast q k, ← Nat.cast_mul,
    ZMod.stdAddChar_apply, ZMod.toCircle_natCast]

private theorem sqrt_mul_inv_sqrt (q : ℕ) [NeZero q] (k : Fin q) :
    ((Real.sqrt q : ℝ) : ℂ) * ((q : ℂ))⁻¹ = ((Real.sqrt q : ℝ) : ℂ)⁻¹ := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast Fin.pos k
  have hsq_ne : ((Real.sqrt q : ℝ) : ℂ) ≠ 0 := by
    have h : (0 : ℝ) < Real.sqrt q := Real.sqrt_pos.mpr hqpos
    exact_mod_cast h.ne'
  have hsq : ((Real.sqrt q : ℝ) : ℂ) * ((Real.sqrt q : ℝ) : ℂ) = (q : ℂ) := by
    have h : Real.sqrt q * Real.sqrt q = (q : ℝ) := Real.mul_self_sqrt hqpos.le
    exact_mod_cast h
  have hq : (q : ℂ) = ((Real.sqrt q : ℝ) : ℂ) * ((Real.sqrt q : ℝ) : ℂ) := hsq.symm
  rw [hq, mul_inv, ← mul_assoc, mul_inv_cancel₀ hsq_ne, one_mul]

private theorem star_sqrt_inv (q : ℕ) :
    star (((Real.sqrt q : ℝ) : ℂ)⁻¹) = ((Real.sqrt q : ℝ) : ℂ)⁻¹ := by
  rw [star_inv₀]
  exact congrArg _ (Complex.conj_ofReal _)

private theorem exp_four_eq_pow (m : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) / 4) = Complex.I ^ m := by
  have harg : (2 * Real.pi * Complex.I * (m : ℂ) / 4)
      = (m : ℂ) * (Real.pi / 2 * Complex.I) := by ring
  rw [harg, Complex.exp_nat_mul, Complex.exp_pi_div_two_mul_I]

private theorem testBit_sum_range (n m : ℕ) (hm : m < 2 ^ n) :
    m = ∑ l ∈ Finset.range n, (if Nat.testBit m l then 2 ^ l else 0) := by
  induction n generalizing m with
  | zero =>
    rw [Finset.sum_range_zero]
    rw [pow_zero] at hm
    omega
  | succ n ih =>
    have h2 : m < 2 ^ n * 2 := by rwa [pow_succ] at hm
    have hm2 : m / 2 < 2 ^ n := by omega
    have ihm := ih (m / 2) hm2
    simp only [Finset.sum_range_succ']
    have h0 : (if Nat.testBit m 0 then 2 ^ 0 else (0 : ℕ)) = m % 2 := by
      rw [Nat.testBit_zero]
      by_cases h : m % 2 = 1
      · simp [h]
      · simp [h]
        omega
    have htail : (∑ k ∈ Finset.range n, (if Nat.testBit m (k + 1) then 2 ^ (k + 1) else (0 : ℕ)))
        = 2 * (m / 2) := by
      rw [ihm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [show k + 1 = Nat.succ k from rfl, Nat.testBit_succ]
      by_cases h : Nat.testBit (m / 2) k = true
      · rw [ite_eq_left h, ite_eq_left h]
        exact pow_succ' 2 k
      · rw [ite_eq_right h, ite_eq_right h, mul_zero]
    rw [h0, htail]
    exact (Nat.div_add_mod m 2).symm

private theorem testBit_sum_univ (n m : ℕ) (hm : m < 2 ^ n) :
    (m : ℂ) = ∑ l : Fin n, (if Nat.testBit m l.val then ((2 ^ l.val : ℕ) : ℂ) else 0) := by
  have hN := testBit_sum_range n m hm
  have hC : (m : ℂ) = ∑ l ∈ Finset.range n, (if Nat.testBit m l then ((2 ^ l : ℕ) : ℂ) else 0) := by
    have h := congrArg (fun t : ℕ => (t : ℂ)) hN
    rw [Nat.cast_sum] at h
    simpa [Nat.cast_ite] using h
  rw [hC]
  have hU := Fin.sum_univ_eq_sum_range
    (fun l : ℕ => (if Nat.testBit m l then ((2 ^ l : ℕ) : ℂ) else 0)) n
  exact hU.symm

private theorem sqrt_two_pow (n : ℕ) : Real.sqrt ((2 : ℝ) ^ n) = (Real.sqrt 2) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Real.sqrt_one]
  | succ n ih =>
    have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
    rw [pow_succ, pow_succ, Real.sqrt_mul hpos, ih]

/-- The quantum Fourier transform matrix acts as `√q` times the inverse
discrete Fourier transform. -/
theorem qftMatrix_mulVec_eq_invDFT (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ)
    (k : Fin q) :
    (qftMatrix q *ᵥ (Φ ∘ ZMod.finEquiv q)) k =
      ((Real.sqrt q : ℝ) : ℂ) * ZMod.dft.symm Φ (ZMod.finEquiv q k) := by
  rw [Matrix.mulVec_apply_eq_sum, ZMod.invDFT_apply]
  simp only [Function.comp_apply, smul_eq_mul]
  have hre : (∑ x : ZMod q, ZMod.stdAddChar (x * ZMod.finEquiv q k) * Φ x)
      = ∑ j : Fin q, ZMod.stdAddChar (ZMod.finEquiv q j * ZMod.finEquiv q k)
        * Φ (ZMod.finEquiv q j) :=
    (((ZMod.finEquiv q).toEquiv.sum_comp
      (fun x => ZMod.stdAddChar (x * ZMod.finEquiv q k) * Φ x)).symm)
  rw [hre, ← mul_assoc, sqrt_mul_inv_sqrt q k, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [qftMatrix_apply, stdAddChar_finEquiv_mul, mul_assoc]
  congr 1
  congr 1
  congr 1
  push_cast
  ring

/-- The conjugate transpose of the quantum Fourier transform matrix acts as
`(√q)⁻¹` times the discrete Fourier transform. -/
theorem conjTranspose_qftMatrix_mulVec_eq_dft (q : ℕ) [NeZero q]
    (Φ : ZMod q → ℂ) (k : Fin q) :
    ((qftMatrix q)ᴴ *ᵥ (Φ ∘ ZMod.finEquiv q)) k =
      ((Real.sqrt q : ℝ) : ℂ)⁻¹ * ZMod.dft Φ (ZMod.finEquiv q k) := by
  rw [Matrix.mulVec_apply_eq_sum, ZMod.dft_apply]
  simp only [Function.comp_apply, smul_eq_mul]
  have hre : (∑ x : ZMod q, ZMod.stdAddChar (-(x * ZMod.finEquiv q k)) * Φ x)
      = ∑ j : Fin q, ZMod.stdAddChar (-(ZMod.finEquiv q j * ZMod.finEquiv q k))
        * Φ (ZMod.finEquiv q j) :=
    (((ZMod.finEquiv q).toEquiv.sum_comp
      (fun x => ZMod.stdAddChar (-(x * ZMod.finEquiv q k)) * Φ x)).symm)
  rw [hre, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.conjTranspose_apply, qftMatrix_apply, star_mul', star_sqrt_inv,
    AddChar.map_neg_eq_conj, starRingEnd_apply, stdAddChar_finEquiv_mul, mul_assoc]
  congr 1
  congr 1
  congr 1
  congr 1
  push_cast
  ring

/-- The four-point quantum Fourier transform has entries `i ^ (j * k) / 2`. -/
theorem qftMatrix_four :
    qftMatrix 4 = Matrix.of fun j k : Fin 4 => Complex.I ^ (j.val * k.val) / 2 := by
  ext j k
  rw [qftMatrix_apply]
  simp only [Matrix.of_apply]
  have h4 : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
    have h42 : ((4 : ℕ) : ℝ) = 2 ^ 2 := by norm_num
    have h2 : (0 : ℝ) ≤ 2 := by norm_num
    rw [h42, Real.sqrt_sq h2]
  have hexp : Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (k : ℂ) / ((4 : ℕ) : ℂ))
      = Complex.I ^ (j.val * k.val) := by
    have harg : (2 * Real.pi * Complex.I * (j : ℂ) * (k : ℂ) / ((4 : ℕ) : ℂ))
        = 2 * Real.pi * Complex.I * (((j.val * k.val : ℕ)) : ℂ) / 4 := by
      push_cast
      ring
    rw [harg]
    exact exp_four_eq_pow _
  rw [hexp, h4]
  push_cast
  ring

/-- Entries of the `2 ^ n`-point quantum Fourier transform factor over the
bits of the row index. -/
theorem qftMatrix_two_pow_apply (n : ℕ) (k j : Fin (2 ^ n)) :
    qftMatrix (2 ^ n) k j =
      ∏ l : Fin n, (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
        (if Nat.testBit k.val l.val then
          Complex.exp (2 * Real.pi * Complex.I * j.val / 2 ^ (n - l.val))
        else 1)) := by
  rw [qftMatrix_apply]
  have hnorm : ∏ _l : Fin n, ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
      = (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ n := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h2n : ((2 ^ n : ℕ) : ℝ) = (2 : ℝ) ^ n := by simp
  have hsqrt : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ n
      = ((Real.sqrt ((2 ^ n : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ := by
    rw [h2n, sqrt_two_pow]
    push_cast
    rw [inv_pow]
  simp only [Finset.prod_mul_distrib, hnorm, hsqrt]
  congr 1
  have hE : ∀ l : Fin n, (if Nat.testBit k.val l.val then
        Complex.exp (2 * Real.pi * Complex.I * j.val / 2 ^ (n - l.val)) else 1)
      = Complex.exp (if Nat.testBit k.val l.val then
        (2 * Real.pi * Complex.I * j.val / 2 ^ (n - l.val) : ℂ) else 0) := by
    intro l
    by_cases h : Nat.testBit k.val l.val = true
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h, Complex.exp_zero]
  simp only [hE, ← Complex.exp_sum]
  congr 1
  have hterm : ∀ l : Fin n, (if Nat.testBit k.val l.val then
        (2 * Real.pi * Complex.I * j.val / 2 ^ (n - l.val) : ℂ) else 0)
      = (2 * Real.pi * Complex.I * (j.val : ℂ) / ((2 ^ n : ℕ) : ℂ))
        * (if Nat.testBit k.val l.val then ((2 ^ l.val : ℕ) : ℂ) else 0) := by
    intro l
    by_cases h : Nat.testBit k.val l.val = true
    · rw [ite_eq_left h, ite_eq_left h]
      push_cast
      have hl : l.val ≤ n := le_of_lt l.isLt
      have hpow : (2 : ℂ) ^ (n - l.val) * (2 : ℂ) ^ l.val = (2 : ℂ) ^ n := by
        rw [← pow_add, Nat.sub_add_cancel hl]
      have h2nl : (2 : ℂ) ^ (n - l.val) ≠ 0 := pow_ne_zero _ (by norm_num)
      have h2n' : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      rw [div_mul_eq_mul_div, div_eq_div_iff h2nl h2n', ← hpow]
      ring
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  simp only [hterm, ← Finset.mul_sum]
  rw [← testBit_sum_univ n k.val k.isLt]
  ring

end MathlibExt.QuantumInformation.Finite.QuantumFourierTransform
