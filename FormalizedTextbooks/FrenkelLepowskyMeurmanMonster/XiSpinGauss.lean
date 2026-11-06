/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Kernel-checked six-dimensional Gauss coefficients and their involutions.
Source: Seysen, arXiv:2002.10921v3, Lemma 9.1 and equation (9.3.1).
The finite computations use the Lean kernel; no external numerical result
is used as a proof of a relation in the named group.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinGaussCoefficients

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- The Gaussian element of any real algebra carrying the grey elementary group. -/
noncomputable def xiGrayGaussian {A : Type*} [Ring A] [Algebra ℝ A]
    (F : Multiplicative XiGrayIndex →* A) : A :=
  (1 / 8 : ℝ) • ∑ a : XiGrayIndex, qSign (xiGrayQuadratic a) • F (ofAdd a)

/-- Gaussian autocorrelation proves the involution in every such representation. -/
theorem xiGrayGaussian_square {A : Type*} [Ring A] [Algebra ℝ A]
    (F : Multiplicative XiGrayIndex →* A) : xiGrayGaussian F * xiGrayGaussian F = 1 := by
  classical
  have hsum :
      (∑ a : XiGrayIndex, qSign (xiGrayQuadratic a) • F (ofAdd a)) *
      (∑ b : XiGrayIndex, qSign (xiGrayQuadratic b) • F (ofAdd b)) = (64 : ℝ) • (1 : A) := by
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      Finset.smul_sum, smul_smul, ← map_mul]
    change (∑ a : XiGrayIndex, ∑ b : XiGrayIndex,
      (qSign (xiGrayQuadratic a) * qSign (xiGrayQuadratic b)) • F (ofAdd (b + a))) = _
    have hreindex (a : XiGrayIndex) :
        (∑ b : XiGrayIndex, (qSign (xiGrayQuadratic a) * qSign (xiGrayQuadratic b)) •
          F (ofAdd (b + a))) =
        ∑ c : XiGrayIndex, (qSign (xiGrayQuadratic a) * qSign (xiGrayQuadratic (a + c))) •
          F (ofAdd c) := by
      have h := Equiv.sum_comp (Equiv.addLeft a)
        (fun b : XiGrayIndex => (qSign (xiGrayQuadratic a) * qSign (xiGrayQuadratic b)) •
          F (ofAdd (b + a)))
      have haa : a + a = 0 := by ext i; exact CharTwo.add_self_eq_zero _
      have hc (c : XiGrayIndex) : a + c + a = c := by
        rw [add_right_comm, haa, zero_add]
      have hleft (c : XiGrayIndex) : (Equiv.addLeft a) c = a + c := rfl
      simpa only [hleft, hc] using h.symm
    simp_rw [hreindex]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, xiGraySign_autocorrelation_real]
    simp
  unfold xiGrayGaussian
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, hsum, smul_smul]
  norm_num

/-- ξ_γ, as an explicit sum of actual cocode spin operators. -/
noncomputable def xiSpinGamma : SpinSpace →ₗ[ℝ] SpinSpace :=
  xiGrayGaussian (spinLinearRepresentation.comp xiGrayModulation)

/-- ξ_g, as an explicit sum of actual normalized code spin operators. -/
noncomputable def xiSpinG : SpinSpace →ₗ[ℝ] SpinSpace :=
  xiGrayGaussian (spinLinearRepresentation.comp xiGrayTranslation)

@[simp] theorem xiSpinGamma_square : xiSpinGamma * xiSpinGamma = 1 :=
  xiGrayGaussian_square _

@[simp] theorem xiSpinG_square : xiSpinG * xiSpinG = 1 :=
  xiGrayGaussian_square _

/-- Column-vector operator corresponding to the sequential source row action ξ_γ ξ_g. -/
noncomputable def xiSpinOperator : SpinSpace →ₗ[ℝ] SpinSpace := xiSpinG * xiSpinGamma

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
