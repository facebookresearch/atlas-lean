/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Explicit Gaussian conjugation, source Seysen §9.3, Lemma 9.4. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.XiSpinGauss

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- Polarization shifts the exact Gauss coefficients. -/
theorem xiGraySign_shift (a p : XiGrayIndex) :
    qSign (xiGrayQuadratic a) * qSign (xiGrayBilinear a p) =
      qSign (xiGrayQuadratic p) * qSign (xiGrayQuadratic (a + p)) := by
  rw [xiGrayQuadratic_add, qSign_add, qSign_add]
  calc
    _ = (qSign (xiGrayQuadratic a) * qSign (xiGrayBilinear a p)) *
        (qSign (xiGrayQuadratic p) * qSign (xiGrayQuadratic p)) := by rw [qSign_sq]; ring
    _ = _ := by ring

/-- Exact conjugation by a Gaussian; the commutation hypothesis is on the
actual represented elements, and will be verified in the coordinate group. -/
theorem xiGrayGaussian_conjugation {A : Type*} [Ring A] [Algebra ℝ A]
    (F : Multiplicative XiGrayIndex →* A) (q : A) (p : XiGrayIndex)
    (hq : ∀ a : XiGrayIndex, F (ofAdd a) * q =
      qSign (xiGrayBilinear a p) • (q * F (ofAdd a))) :
    xiGrayGaussian F * q * xiGrayGaussian F =
      qSign (xiGrayQuadratic p) • (q * F (ofAdd p)) := by
  classical
  have hshift :
      (∑ a : XiGrayIndex, (qSign (xiGrayQuadratic a) * qSign (xiGrayBilinear a p)) •
        F (ofAdd a)) =
      qSign (xiGrayQuadratic p) •
        (F (ofAdd p) * ∑ a : XiGrayIndex, qSign (xiGrayQuadratic a) • F (ofAdd a)) := by
    simp only [Finset.mul_sum, mul_smul_comm, ← map_mul, Finset.smul_sum, smul_smul]
    change (∑ a : XiGrayIndex, (qSign (xiGrayQuadratic a) * qSign (xiGrayBilinear a p)) •
      F (ofAdd a)) =
      ∑ a : XiGrayIndex, (qSign (xiGrayQuadratic p) * qSign (xiGrayQuadratic a)) •
        F (ofAdd (p + a))
    have h := Equiv.sum_comp (Equiv.addLeft p)
      (fun a : XiGrayIndex => (qSign (xiGrayQuadratic a) * qSign (xiGrayBilinear a p)) •
        F (ofAdd a))
    have hpp : p + p = 0 := by ext i; exact CharTwo.add_self_eq_zero _
    have hleft (a : XiGrayIndex) : (Equiv.addLeft p) a = p + a := rfl
    simpa only [hleft, xiGraySign_shift, add_comm _ p,
      ← add_assoc, hpp, zero_add] using h.symm
  have hintertwine : xiGrayGaussian F * q =
      qSign (xiGrayQuadratic p) • (q * F (ofAdd p) * xiGrayGaussian F) := by
    unfold xiGrayGaussian
    simp only [smul_mul_assoc, Finset.sum_mul, hq, smul_smul]
    rw [show (∑ a : XiGrayIndex,
        (qSign (xiGrayQuadratic a) * qSign (xiGrayBilinear a p)) • (q * F (ofAdd a))) =
        q * ∑ a : XiGrayIndex,
          (qSign (xiGrayQuadratic a) * qSign (xiGrayBilinear a p)) • F (ofAdd a) by
      simp only [Finset.mul_sum, mul_smul_comm]]
    rw [hshift]
    simp only [mul_smul_comm, smul_smul, mul_assoc]
    congr 1
    ring
  rw [hintertwine, smul_mul_assoc, mul_assoc, xiGrayGaussian_square, mul_one]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
