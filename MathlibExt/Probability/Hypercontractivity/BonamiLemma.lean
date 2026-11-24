/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Hypercontractivity.SmallSetExpansion
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# The (2,4)-Hypercontractivity Theorem and the Bonami Lemma

The proved Bonami–Beckner inequality on the uniform cube is the `(4/3, 2)` case at
`ρ = 1/√3`: `‖T_ρ f‖₂ ≤ ‖f‖_{4/3}` (`StatMech.Probability.vtp_hypercontractivity`). Because `T_ρ`
is self-adjoint, Hölder duality turns it into the `(2, 4)` case `‖T_{1/√3} f‖₄ ≤ ‖f‖₂`:
for `h = T_ρ f`,
`𝔼[h⁴] = 𝔼[T_ρ f · h³] = 𝔼[f · T_ρ(h³)] ≤ ‖f‖₂ ‖T_ρ(h³)‖₂ ≤ ‖f‖₂ ‖h³‖_{4/3} = ‖f‖₂ 𝔼[h⁴]^{3/4}`.
Applying it to `g = T_{√3} f` (so `T_{1/√3} g = f`) gives the Bonami Lemma
`‖f‖₄ ≤ √3^k ‖f‖₂` for `f` of degree at most `k`, since `‖g‖₂² = ∑_S 3^|S| f̂(S)² ≤ 3^k ‖f‖₂²`.

Both results are stated in fourth-power form, which avoids `L⁴` norms.

## Main statements

* `BooleanCube.expect_boolNoiseOp_pow_four_le`: `𝔼[(T_{1/√3} f)⁴] ≤ 𝔼[f²]²`.
* `BooleanCube.bonami_lemma`: `𝔼[f⁴] ≤ 9^k 𝔼[f²]²` for `f` of degree at most `k`.

## References

* A. Bonami, *Étude des coefficients de Fourier des fonctions de `L^p(G)`*, Ann. Inst. Fourier
  20 (1970), 335-402.
* R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014
  (arXiv:2105.10386), Chapter 9: the Bonami Lemma and the (2,4)- and (4/3,2)-Hypercontractivity
  Theorems (Sections 9.1 and 9.2), and Proposition 9.19 for the duality.
-/

@[expose] public section

namespace BooleanCube

open scoped BigOperators
open StatMech.Probability

variable {n : ℕ}

/-- The `L^{4/3}` norm of a cube is the fourth moment to the power `3/4`. -/
private theorem bnt_qnorm_four_thirds_pow_three (h : BoolCube n → ℝ) :
    bnt_qnorm (4 / 3) (fun x => h x ^ 3) = (𝔼 x, h x ^ 4) ^ ((3 : ℝ) / 4) := by
  have hpow : bnt_qnormPow (4 / 3) (fun x => h x ^ 3) = 𝔼 x, h x ^ 4 := by
    rw [bnt_qnormPow, bnt_uexp_eq_expect]
    refine Finset.expect_congr rfl fun x _ => ?_
    have h3 : |h x ^ 3| ^ ((4 : ℝ) / 3) = |h x| ^ (4 : ℕ) := by
      rw [abs_pow, ← Real.rpow_natCast_mul (abs_nonneg _)]
      norm_num
    rw [h3, pow_abs, abs_of_nonneg (by positivity)]
  rw [bnt_qnorm, hpow]
  norm_num

/-- **(2,4)-Hypercontractivity Theorem.** For every `f : BoolCube n → ℝ`,
`‖T_{1/√3} f‖₄ ≤ ‖f‖₂`, stated in fourth-power form `𝔼[(T_{1/√3} f)⁴] ≤ 𝔼[f²]²` (R. O'Donnell,
*Analysis of Boolean Functions*, 2014, (2,4)-Hypercontractivity Theorem, Section 9.2; obtained
here from the (4/3,2) case by the duality of Proposition 9.19). -/
theorem expect_boolNoiseOp_pow_four_le (f : BoolCube n → ℝ) :
    𝔼 x, boolNoiseOp (Real.sqrt (1 / 3)) f x ^ 4 ≤ (𝔼 x, f x ^ 2) ^ 2 := by
  set ρ := Real.sqrt (1 / 3) with hρ
  set h := boolNoiseOp ρ f with hh
  set M := 𝔼 x, h x ^ 4 with hM
  set A := 𝔼 x, f x ^ 2 with hA
  have hρ2 : ρ ^ 2 = 1 / 3 := Real.sq_sqrt (by norm_num)
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ ≤ 1 := Real.sqrt_le_one.mpr (by norm_num)
  have hM0 : 0 ≤ M := Finset.expect_nonneg fun _ _ => by positivity
  have hA0 : 0 ≤ A := Finset.expect_nonneg fun _ _ => sq_nonneg _
  -- `M = 𝔼[f · T_ρ (h³)]`, by self-adjointness of `T_ρ`.
  have hdual : M = 𝔼 x, f x * boolNoiseOp ρ (fun y => h y ^ 3) x := by
    rw [← expect_boolNoiseOp_mul_comm, hM]
    refine Finset.expect_congr rfl fun x _ => ?_
    ring
  -- Hypercontractivity applied to `h³`.
  have hhc : 𝔼 x, boolNoiseOp ρ (fun y => h y ^ 3) x ^ 2 ≤ M ^ ((3 : ℝ) / 2) := by
    have hc := vtp_hypercontractivity hρ0 hρ1 n (fun y => h y ^ 3)
    rw [bnt_noiseOp_eq_boolNoiseOp, hρ2] at hc
    have hc' : bnt_qnorm 2 (boolNoiseOp ρ fun y => h y ^ 3) ≤ M ^ ((3 : ℝ) / 4) := by
      have h43 : (1 : ℝ) + 1 / 3 = 4 / 3 := by norm_num
      rw [h43, bnt_qnorm_four_thirds_pow_three] at hc
      exact hc
    calc 𝔼 x, boolNoiseOp ρ (fun y => h y ^ 3) x ^ 2
        = bnt_qnorm 2 (boolNoiseOp ρ fun y => h y ^ 3) ^ 2 := (bnt_qnorm_two_sq _).symm
      _ ≤ (M ^ ((3 : ℝ) / 4)) ^ 2 := pow_le_pow_left₀ (bnt_qnorm_nonneg _ _) hc' 2
      _ = M ^ ((3 : ℝ) / 2) := by
        rw [← Real.rpow_mul_natCast hM0]
        norm_num
  -- Cauchy–Schwarz: `M² ≤ A · M^{3/2}`.
  have hcs : M ^ 2 ≤ A * M ^ ((3 : ℝ) / 2) := by
    calc M ^ 2 = (𝔼 x, f x * boolNoiseOp ρ (fun y => h y ^ 3) x) ^ 2 := by rw [← hdual]
      _ ≤ A * 𝔼 x, boolNoiseOp ρ (fun y => h y ^ 3) x ^ 2 :=
          Finset.expect_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ A * M ^ ((3 : ℝ) / 2) := mul_le_mul_of_nonneg_left hhc hA0
  rcases hM0.eq_or_lt with hz | hpos
  · rw [← hz]
    positivity
  · have hsplit : M ^ 2 = M ^ ((1 : ℝ) / 2) * M ^ ((3 : ℝ) / 2) := by
      rw [← Real.rpow_add hpos, ← Real.rpow_natCast]
      norm_num
    have h32 : 0 < M ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hpos _
    have hhalf : M ^ ((1 : ℝ) / 2) ≤ A := by
      rw [hsplit] at hcs
      exact le_of_mul_le_mul_right hcs h32
    have hsq : (M ^ ((1 : ℝ) / 2)) ^ 2 = M := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hM0]
    calc M = (M ^ ((1 : ℝ) / 2)) ^ 2 := hsq.symm
      _ ≤ A ^ 2 := pow_le_pow_left₀ (Real.rpow_nonneg hM0 _) hhalf 2

/-- **Bonami Lemma.** If `f : BoolCube n → ℝ` has degree at most `k` (all Fourier coefficients
on sets of size greater than `k` vanish), then `‖f‖₄ ≤ √3^k ‖f‖₂`; equivalently, raising both
sides to the fourth power, `𝔼[f⁴] ≤ 9^k (𝔼[f²])²` (R. O'Donnell, *Analysis of Boolean
Functions*, 2014, Bonami Lemma, Chapter 9 introduction, proved in Section 9.1). -/
theorem bonami_lemma {n k : ℕ} (f : BoolCube n → ℝ) (hf : MultilinearDegreeLE n f k) :
    𝔼 x, f x ^ 4 ≤ 9 ^ k * (𝔼 x, f x ^ 2) ^ 2 := by
  set g := boolNoiseOp (Real.sqrt 3) f with hg
  have hinv : boolNoiseOp (Real.sqrt (1 / 3)) g = f := by
    rw [hg, boolNoiseOp_boolNoiseOp, ← Real.sqrt_mul (by norm_num)]
    norm_num
  have h4 := expect_boolNoiseOp_pow_four_le g
  rw [hinv] at h4
  have hg2 : 𝔼 x, g x ^ 2 ≤ 3 ^ k * 𝔼 x, f x ^ 2 := by
    rw [expect_sq_eq_sum_boolFourierCoeff_sq, expect_sq_eq_sum_boolFourierCoeff_sq,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun S _ => ?_
    rw [hg, boolFourierCoeff_boolNoiseOp, mul_pow, ← pow_mul,
      show Real.sqrt 3 ^ (S.card * 2) = 3 ^ S.card by
        rw [pow_mul', Real.sq_sqrt (by norm_num)]]
    by_cases hS : k < S.card
    · rw [hf S hS]
      simp
    · have hle : (3 : ℝ) ^ S.card ≤ 3 ^ k := pow_le_pow_right₀ (by norm_num) (not_lt.mp hS)
      exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  have hg0 : 0 ≤ 𝔼 x, g x ^ 2 := Finset.expect_nonneg fun _ _ => sq_nonneg _
  calc 𝔼 x, f x ^ 4 ≤ (𝔼 x, g x ^ 2) ^ 2 := h4
    _ ≤ (3 ^ k * 𝔼 x, f x ^ 2) ^ 2 := pow_le_pow_left₀ hg0 hg2 2
    _ = 9 ^ k * (𝔼 x, f x ^ 2) ^ 2 := by
      rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul]
      norm_num

end BooleanCube
