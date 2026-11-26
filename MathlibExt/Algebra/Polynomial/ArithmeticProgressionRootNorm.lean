/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Complex.Norm
import MathlibExt.Algebra.Polynomial.ArithmeticProgressionAuxiliaryRoot
import MathlibExt.Algebra.Polynomial.ArithmeticProgressionRootPower
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Root norm bound for arithmetic-progression polynomials

The boundary identity controls the modulus of a root by the positive root of the auxiliary
real equation. On the boundary, equality in the norm comparison forces a negative real zero.
-/

open Polynomial

namespace MetaMathlibExt

private theorem norm_affine_sq (a b : ℝ) (z : ℂ) :
    ‖(a : ℂ) * z - (b : ℂ)‖ ^ 2 = a ^ 2 * ‖z‖ ^ 2 - 2 * a * b * z.re + b ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, add_zero]
  ring

/-- **Bound on the zeros of the arithmetic-progression polynomial.** Let $m \ge 2$, let $a$, $d$
be integers with $0 < d \le a$, and let $\lambda > 0$ be a real number with
$a \lambda^{m+2} + (a - d) \lambda^{m+1} - (a + (m + 1)d) \lambda - (a + md) = 0$. Then every
complex zero $z$ of $A_m(x) = a x^m + (a + d) x^{m-1} + \cdots + (a + md)$ satisfies
$|z| \le \lambda$, and $|z| = \lambda$ only if $z = -\lambda$.

Source: Hiroaki Kakuma, *Irreducibility of Polynomials with Coefficients in a Positive
Arithmetic Progression*, INTEGERS 26 (2026), Article A92, Proposition 2
(`integers-2026-A92-prop-2`). -/
public theorem arithProgPoly_root_norm_le {m a d : ℕ} (hm : 2 ≤ m) (hd : 0 < d)
    (hda : d ≤ a) (lam : ℝ) (hlam : 0 < lam)
    (hG : (a : ℝ) * lam ^ (m + 2) + ((a : ℝ) - d) * lam ^ (m + 1) -
      ((a : ℝ) + (m + 1) * d) * lam - ((a : ℝ) + m * d) = 0) (z : ℂ)
    (hz : aeval z (∑ i ∈ Finset.range (m + 1), C ((a : ℤ) + i * d) * X ^ (m - i)) = 0) :
    ‖z‖ ≤ lam ∧ (‖z‖ = lam → z = -(lam : ℂ)) := by
  have h1 := (arithProgPoly_eq3_existsUnique_pos hm hd hda).2 lam hlam hG
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  let A : ℝ := a
  let B : ℝ := a - d
  let U : ℝ := a + (m + 1) * d
  let V : ℝ := a + m * d
  let r : ℝ := ‖z‖
  let p : ℝ := ‖(A : ℂ) * z - (B : ℂ)‖
  let q : ℝ := ‖(U : ℂ) * z - (V : ℂ)‖
  have hA : 0 < A := by dsimp [A]; exact_mod_cast hd.trans_le hda
  have hB : 0 ≤ B := sub_nonneg.mpr (by exact_mod_cast hda)
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  have hBA : B < A := by dsimp [A, B]; linarith
  have hdet : 0 < A * V - B * U := by
    have heq : A * V - B * U = ((m : ℝ) + 1) * (d : ℝ) ^ 2 := by
      dsimp [A, B, U, V]
      ring
    rw [heq]
    positivity
  have hac : 0 < A * U - B * V := by
    have heq : A * U - B * V = (d : ℝ) * (A + V) := by
      dsimp [A, B, U, V]
      ring
    rw [heq]
    positivity
  have haux : lam ^ (m + 1) * (A * lam + B) = U * lam + V := by
    change (a : ℝ) * lam ^ (m + 2) + B * lam ^ (m + 1) - U * lam - V = 0 at hG
    rw [show m + 2 = m + 1 + 1 from rfl, pow_succ lam (m + 1)] at hG
    linear_combination hG
  have hsum : 0 ≤ r + z.re := by
    have hre := (abs_le.mp (Complex.abs_re_le_norm z)).1
    change -r ≤ z.re at hre
    linarith
  -- The norm comparison is sharp precisely on the negative real axis.
  have hdefect : (U * r + V) ^ 2 * p ^ 2 - (A * r + B) ^ 2 * q ^ 2 =
      2 * (r + z.re) * (A * V - B * U) * (A * U * r ^ 2 - B * V) := by
    change (U * r + V) ^ 2 * ‖(A : ℂ) * z - (B : ℂ)‖ ^ 2 -
      (A * r + B) ^ 2 * ‖(U : ℂ) * z - (V : ℂ)‖ ^ 2 = _
    rw [norm_affine_sq, norm_affine_sq]
    change (U * r + V) ^ 2 * (A ^ 2 * r ^ 2 - 2 * A * B * z.re + B ^ 2) -
      (A * r + B) ^ 2 * (U ^ 2 * r ^ 2 - 2 * U * V * z.re + V ^ 2) = _
    ring
  by_cases hr : lam ≤ r
  · have hr1 : 1 < r := h1.trans_le hr
    have hpos : 0 < A * U * r ^ 2 - B * V := by
      have hrsq : 0 ≤ r ^ 2 - 1 := by nlinarith only [hr1, sq_nonneg (r - 1)]
      nlinarith only [hac, mul_nonneg (mul_pos hA hU).le hrsq]
    have hden : (A : ℂ) * z - (B : ℂ) ≠ 0 := by
      intro hzero
      have heq := congrArg (fun w : ℂ ↦ ‖w‖) (sub_eq_zero.mp hzero)
      rw [Complex.norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos hA, abs_of_nonneg hB] at heq
      change A * r = B at heq
      have hlt := mul_lt_mul_of_pos_left hr1 hA
      rw [mul_one, heq] at hlt
      exact hBA.not_gt hlt
    have hpow : z ^ (m + 1) = ((U : ℂ) * z - (V : ℂ)) / ((A : ℂ) * z - (B : ℂ)) := by
      dsimp [A, B, U, V]
      push_cast
      exact arithProgPoly_root_pow_eq m a d hd z (Or.inl hz)
    have hnorm := congrArg (fun w : ℂ ↦ ‖w‖) ((eq_div_iff hden).mp hpow)
    rw [Complex.norm_mul, Complex.norm_pow] at hnorm
    change r ^ (m + 1) * p = q at hnorm
    have hp : 0 < p := norm_pos_iff.mpr hden
    have hAr : 0 < A * r + B := by have : 0 < r := hlam.trans_le hr; positivity
    have hUr : 0 < U * r + V := by have : 0 < r := hlam.trans_le hr; positivity
    have hnonneg : 0 ≤ (U * r + V) ^ 2 * p ^ 2 - (A * r + B) ^ 2 * q ^ 2 := by
      rw [hdefect]
      positivity
    have hcross : (A * r + B) * q ≤ (U * r + V) * p := by
      by_contra! hlt
      have hs := mul_lt_mul hlt hlt.le (mul_pos hUr hp) ((mul_pos hUr hp).trans hlt).le
      nlinarith only [hs, hnonneg]
    have hbound : r ^ (m + 1) * (A * r + B) ≤ U * r + V := by
      rw [← hnorm, ← mul_left_comm, ← mul_assoc] at hcross
      exact le_of_mul_le_mul_right hcross hp
    have hmono : (U * r + V) * (A * lam + B) ≤ (U * lam + V) * (A * r + B) := by
      nlinarith only [mul_nonneg hdet.le (sub_nonneg.mpr hr)]
    have hAl : 0 < A * lam + B := by positivity
    have hpowle : r ^ (m + 1) ≤ lam ^ (m + 1) := by
      have hcomp := (mul_le_mul_of_nonneg_right hbound hAl.le).trans hmono
      rw [← haux] at hcomp
      exact le_of_mul_le_mul_right (by simpa only [mul_assoc, mul_comm (A * r + B)] using hcomp)
        (mul_pos hAr hAl)
    have hle : r ≤ lam := by
      by_contra! hlt
      exact (not_lt_of_ge hpowle) (pow_lt_pow_left₀ hlt hlam.le (Nat.succ_ne_zero m))
    refine ⟨hle, fun heq ↦ ?_⟩
    change r = lam at heq
    have hqeq : (A * r + B) * q = (U * r + V) * p := by
      rw [← hnorm, heq, ← haux]
      ring
    have hzero : (U * r + V) ^ 2 * p ^ 2 - (A * r + B) ^ 2 * q ^ 2 = 0 := by
      rw [← mul_pow, ← mul_pow, hqeq, sub_self]
    rw [hdefect] at hzero
    have hx : r + z.re = 0 := by
      rcases mul_eq_zero.mp hzero with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact (mul_eq_zero.mp h).resolve_left (by norm_num)
        · exact (hdet.ne' h).elim
      · exact (hpos.ne' h).elim
    have hre : z.re = -r := by linarith
    have him : z.im = 0 := by
      have hs := Complex.sq_norm_sub_sq_re z
      change r ^ 2 - z.re ^ 2 = z.im ^ 2 at hs
      rw [hre, neg_sq, sub_self] at hs
      nlinarith only [hs, sq_nonneg (z.im - 1), sq_nonneg (z.im + 1)]
    apply Complex.ext
    · simpa only [Complex.neg_re, Complex.ofReal_re, heq] using hre
    · simpa only [Complex.neg_im, Complex.ofReal_im, neg_zero] using him
  · exact ⟨le_of_lt (lt_of_not_ge hr), fun heq ↦ (hr heq.symm.le).elim⟩

end MetaMathlibExt
