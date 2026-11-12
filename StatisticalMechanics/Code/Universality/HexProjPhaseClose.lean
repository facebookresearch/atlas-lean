/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































































import Code.Universality.HexBoundaryPhases
import Code.Universality.HexBoundaryIdentityClose

namespace StatMech.Universality

open Complex
open scoped Real BigOperators











theorem hpp_slantEps_fold :
    (1/2 : ℂ) * hexUnit 3 * Complex.exp ((-(hbi_sigma * (2*Real.pi/3)) : ℝ) * Complex.I)
      = (1/2 : ℂ) * Complex.exp ((3*Real.pi/4 : ℝ) * Complex.I) := by
  unfold hexUnit hbi_sigma
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast; ring



theorem hpp_slantEpsBar_fold :
    (1/2 : ℂ) * hexUnit (-1) * Complex.exp ((hbi_sigma * (2*Real.pi/3) : ℝ) * Complex.I)
      = (1/2 : ℂ) * Complex.exp ((Real.pi/4 : ℝ) * Complex.I) := by
  unfold hexUnit hbi_sigma
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast; ring





theorem hpp_slant_madeReal :
    (1/2 : ℂ) * Complex.exp ((3*Real.pi/4 : ℝ) * Complex.I)
        + (1/2 : ℂ) * Complex.exp ((Real.pi/4 : ℝ) * Complex.I)
      = Complex.I * ((hexBdryCt : ℝ) : ℂ) := by
  have hIexp : Complex.exp ((Real.pi/2 : ℝ) * Complex.I) = Complex.I := by
    rw [show ((Real.pi/2:ℝ):ℂ)*Complex.I = (↑Real.pi/2:ℂ)*Complex.I by push_cast; ring]
    exact exp_pi_div_two_mul_I
  have h3 : Complex.exp ((3*Real.pi/4 : ℝ) * Complex.I)
      = Complex.exp ((Real.pi/2 : ℝ) * Complex.I) * Complex.exp ((Real.pi/4 : ℝ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have h1 : Complex.exp ((Real.pi/4 : ℝ) * Complex.I)
      = Complex.exp ((Real.pi/2 : ℝ) * Complex.I) * Complex.exp ((-(Real.pi/4) : ℝ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [h3]
  nth_rewrite 2 [h1]
  rw [hIexp]
  have hsum : Complex.exp ((Real.pi/4 : ℝ) * Complex.I)
      + Complex.exp ((-(Real.pi/4) : ℝ) * Complex.I) = 2 * (Real.cos (Real.pi/4) : ℂ) :=
    hexExpI_add_neg (Real.pi/4)
  unfold hexBdryCt
  calc (1/2:ℂ) * (Complex.I * Complex.exp ((Real.pi/4:ℝ)*Complex.I))
        + (1/2:ℂ) * (Complex.I * Complex.exp ((-(Real.pi/4):ℝ)*Complex.I))
      = Complex.I * (1/2 : ℂ) * (Complex.exp ((Real.pi/4:ℝ)*Complex.I)
          + Complex.exp ((-(Real.pi/4):ℝ)*Complex.I)) := by ring
    _ = Complex.I * (1/2 : ℂ) * (2 * (Real.cos (Real.pi/4):ℂ)) := by rw [hsum]
    _ = Complex.I * ((Real.cos (Real.pi/4):ℝ):ℂ) := by push_cast; ring















theorem hpp_slantProj_combined (E : ℝ) :
    (1/2 : ℂ) * hexUnit 3
        * (Complex.exp ((-(hbi_sigma * (2*Real.pi/3)) : ℝ) * Complex.I) * ((E/2 : ℝ) : ℂ))
      + (1/2 : ℂ) * hexUnit (-1)
        * (Complex.exp ((hbi_sigma * (2*Real.pi/3) : ℝ) * Complex.I) * ((E/2 : ℝ) : ℂ))
      = Complex.I * ((hexBdryCt * (E/2) : ℝ) : ℂ) := by
  rw [show (1/2 : ℂ) * hexUnit 3
          * (Complex.exp ((-(hbi_sigma * (2*Real.pi/3)) : ℝ) * Complex.I) * ((E/2 : ℝ) : ℂ))
        = ((1/2 : ℂ) * hexUnit 3 * Complex.exp ((-(hbi_sigma * (2*Real.pi/3)) : ℝ) * Complex.I))
            * ((E/2 : ℝ) : ℂ) by ring,
      show (1/2 : ℂ) * hexUnit (-1)
          * (Complex.exp ((hbi_sigma * (2*Real.pi/3) : ℝ) * Complex.I) * ((E/2 : ℝ) : ℂ))
        = ((1/2 : ℂ) * hexUnit (-1) * Complex.exp ((hbi_sigma * (2*Real.pi/3) : ℝ) * Complex.I))
            * ((E/2 : ℝ) : ℂ) by ring]
  rw [hpp_slantEps_fold, hpp_slantEpsBar_fold]
  rw [show (1/2 : ℂ) * Complex.exp ((3*Real.pi/4 : ℝ) * Complex.I) * ((E/2 : ℝ) : ℂ)
        + (1/2 : ℂ) * Complex.exp ((Real.pi/4 : ℝ) * Complex.I) * ((E/2 : ℝ) : ℂ)
      = ((1/2 : ℂ) * Complex.exp ((3*Real.pi/4 : ℝ) * Complex.I)
          + (1/2 : ℂ) * Complex.exp ((Real.pi/4 : ℝ) * Complex.I)) * ((E/2 : ℝ) : ℂ) by ring]
  rw [hpp_slant_madeReal]
  push_cast; ring_nf














theorem hpp_singleSlantProj_re_ne_zero (r : ℝ) (hr : 0 < r) :
    ((1/2 : ℂ) * hexUnit 3
        * (Complex.exp ((-(hbi_sigma * (2*Real.pi/3)) : ℝ) * Complex.I) * (r:ℂ))).re ≠ 0 := by
  rw [show (1/2 : ℂ) * hexUnit 3 * (Complex.exp ((-(hbi_sigma * (2*Real.pi/3)) : ℝ) * Complex.I) * (r:ℂ))
      = ((1/2 : ℂ) * hexUnit 3 * Complex.exp ((-(hbi_sigma * (2*Real.pi/3)) : ℝ) * Complex.I)) * (r:ℂ) by ring,
      hpp_slantEps_fold]
  rw [show (1/2 : ℂ) * Complex.exp ((3*Real.pi/4 : ℝ) * Complex.I) * (r:ℂ)
      = ((r/2 : ℝ):ℂ) * Complex.exp ((3*Real.pi/4 : ℝ) * Complex.I) by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I]
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im]
  have hcos : Real.cos (3*Real.pi/4) < 0 := by
    rw [show (3*Real.pi/4 : ℝ) = Real.pi - Real.pi/4 by ring, Real.cos_pi_sub]
    have : 0 < Real.cos (Real.pi/4) := by rw [Real.cos_pi_div_four]; positivity
    linarith
  have hlt : (r/2) * Real.cos (3*Real.pi/4) < 0 := mul_neg_of_pos_of_neg (by linarith) hcos
  intro hzero
  nlinarith [hlt]









theorem hpp_alphaDir : (1/2 : ℂ) * hexUnit 4 = -(Complex.I / 2) := by
  unfold hexUnit
  rw [show Complex.I * ((Real.pi:ℂ)/6 + (((4:ℤ):ℝ):ℂ) * ((Real.pi:ℂ)/3))
        = ((3 * (Real.pi/2) : ℝ):ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I]
  rw [show (3 * (Real.pi/2) : ℝ) = Real.pi + Real.pi/2 by ring]
  rw [Real.cos_add, Real.sin_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast; ring



theorem hpp_topDir : (1/2 : ℂ) * hexUnit 1 = Complex.I / 2 := by
  unfold hexUnit
  rw [show Complex.I * ((Real.pi:ℂ)/6 + (((1:ℤ):ℝ):ℂ) * ((Real.pi:ℂ)/3))
        = ((Real.pi/2 : ℝ):ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I, Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast; ring










theorem hpp_alphaProj (A : ℝ) :
    (1/2 : ℂ) * hexUnit 4 * (((1 - hexBdryCl * A : ℝ)) : ℂ)
      = Complex.I * ((-(1 - hexBdryCl * A)/2 : ℝ) : ℂ) := by
  rw [hpp_alphaDir]; push_cast; ring






theorem hpp_topProj (B : ℝ) :
    (1/2 : ℂ) * hexUnit 1 * ((B : ℝ) : ℂ) = Complex.I * ((B/2 : ℝ) : ℂ) := by
  rw [hpp_topDir]; push_cast; ring





















structure hpp_BoundaryIntegralData where
  
  A : ℝ
  
  B : ℝ
  
  E : ℝ
  
  Fa : ℝ
  
  alphaFSum : ℂ
  
  alphaFSum_eq : alphaFSum = ((Fa - hexBdryCl * A : ℝ) : ℂ)
  
  betaFSum : ℂ
  
  betaFSum_eq : betaFSum = ((B : ℝ) : ℂ)
  
  epsFSum : ℂ
  
  epsFSum_eq : epsFSum
    = Complex.exp ((-(hbi_sigma * (2*Real.pi/3)) : ℝ) * Complex.I) * ((E/2 : ℝ) : ℂ)
  
  epsbarFSum : ℂ
  
  epsbarFSum_eq : epsbarFSum
    = Complex.exp ((hbi_sigma * (2*Real.pi/3) : ℝ) * Complex.I) * ((E/2 : ℝ) : ℂ)

namespace hpp_BoundaryIntegralData

variable (D : hpp_BoundaryIntegralData)

















theorem boundaryIntegral_eq :
    (1/2 : ℂ) * hexUnit 4 * D.alphaFSum
        + (1/2 : ℂ) * hexUnit 1 * D.betaFSum
        + ((1/2 : ℂ) * hexUnit 3 * D.epsFSum + (1/2 : ℂ) * hexUnit (-1) * D.epsbarFSum)
      = Complex.I * ((((hexBdryCl * D.A + hexBdryCt * D.E + D.B : ℝ) - (D.Fa : ℝ))/2 : ℝ) : ℂ) := by
  rw [D.alphaFSum_eq, D.betaFSum_eq, D.epsFSum_eq, D.epsbarFSum_eq]
  
  rw [show (1/2 : ℂ) * hexUnit 3
            * (Complex.exp ((-(hbi_sigma * (2*Real.pi/3)) : ℝ) * Complex.I) * ((D.E/2 : ℝ) : ℂ))
          + (1/2 : ℂ) * hexUnit (-1)
            * (Complex.exp ((hbi_sigma * (2*Real.pi/3) : ℝ) * Complex.I) * ((D.E/2 : ℝ) : ℂ))
        = Complex.I * ((hexBdryCt * (D.E/2) : ℝ) : ℂ) from hpp_slantProj_combined D.E]
  
  rw [hpp_alphaDir, hpp_topDir]
  push_cast; ring









theorem boundaryIdentity (hFa : D.Fa = 1)
    (hvanish : (1/2 : ℂ) * hexUnit 4 * D.alphaFSum
        + (1/2 : ℂ) * hexUnit 1 * D.betaFSum
        + ((1/2 : ℂ) * hexUnit 3 * D.epsFSum + (1/2 : ℂ) * hexUnit (-1) * D.epsbarFSum) = 0) :
    hexBdryCl * D.A + hexBdryCt * D.E + D.B = 1 := by
  have heq := D.boundaryIntegral_eq
  rw [hvanish] at heq
  
  have hzero : (((hexBdryCl * D.A + hexBdryCt * D.E + D.B : ℝ) - (D.Fa : ℝ))/2 : ℝ) = 0 := by
    have : ((((hexBdryCl * D.A + hexBdryCt * D.E + D.B : ℝ) - (D.Fa : ℝ))/2 : ℝ) : ℂ) = 0 := by
      have h := heq.symm
      rcases mul_eq_zero.mp h with h1 | h2
      · exact absurd h1 Complex.I_ne_zero
      · exact h2
    exact_mod_cast this
  rw [hFa] at hzero
  linarith [hzero]

end hpp_BoundaryIntegralData

















theorem hpp_hbdry (D : ℕ → hpp_BoundaryIntegralData)
    (hFa : ∀ v, 1 ≤ v → (D v).Fa = 1)
    (hvanish : ∀ v, 1 ≤ v →
      (1/2 : ℂ) * hexUnit 4 * (D v).alphaFSum
        + (1/2 : ℂ) * hexUnit 1 * (D v).betaFSum
        + ((1/2 : ℂ) * hexUnit 3 * (D v).epsFSum + (1/2 : ℂ) * hexUnit (-1) * (D v).epsbarFSum) = 0) :
    ∀ v, 1 ≤ v →
      hexBdryCl * (D v).A + hexBdryCt * (D v).E + (D v).B = 1 := by
  intro v hv
  exact (D v).boundaryIdentity (hFa v hv) (hvanish v hv)











noncomputable def hpp_witness : hpp_BoundaryIntegralData where
  A := 0
  B := 1
  E := 0
  Fa := 1
  alphaFSum := ((1 - hexBdryCl * 0 : ℝ) : ℂ)
  alphaFSum_eq := by norm_num
  betaFSum := ((1 : ℝ) : ℂ)
  betaFSum_eq := rfl
  epsFSum := Complex.exp ((-(hbi_sigma * (2*Real.pi/3)) : ℝ) * Complex.I) * (((0:ℝ)/2 : ℝ) : ℂ)
  epsFSum_eq := rfl
  epsbarFSum := Complex.exp ((hbi_sigma * (2*Real.pi/3) : ℝ) * Complex.I) * (((0:ℝ)/2 : ℝ) : ℂ)
  epsbarFSum_eq := rfl



theorem hpp_witness_vanish :
    (1/2 : ℂ) * hexUnit 4 * hpp_witness.alphaFSum
      + (1/2 : ℂ) * hexUnit 1 * hpp_witness.betaFSum
      + ((1/2 : ℂ) * hexUnit 3 * hpp_witness.epsFSum
          + (1/2 : ℂ) * hexUnit (-1) * hpp_witness.epsbarFSum) = 0 := by
  change (1 / 2 : ℂ) * hexUnit 4 * (((1 - hexBdryCl * 0 : ℝ) : ℂ))
      + (1 / 2 : ℂ) * hexUnit 1 * (((1 : ℝ) : ℂ))
      + ((1 / 2 : ℂ) * hexUnit 3
            * (Complex.exp ((-(hbi_sigma * (2 * Real.pi / 3)) : ℝ) * Complex.I) * (((0:ℝ) / 2 : ℝ) : ℂ))
          + (1 / 2 : ℂ) * hexUnit (-1)
            * (Complex.exp ((hbi_sigma * (2 * Real.pi / 3) : ℝ) * Complex.I) * (((0:ℝ) / 2 : ℝ) : ℂ))) = 0
  rw [hpp_alphaDir, hpp_topDir]
  simp only [mul_zero, zero_div, Complex.ofReal_zero, mul_zero, add_zero]
  push_cast; ring



theorem hpp_witness_identity :
    hexBdryCl * hpp_witness.A + hexBdryCt * hpp_witness.E + hpp_witness.B = 1 :=
  hpp_witness.boundaryIdentity rfl hpp_witness_vanish

end StatMech.Universality
