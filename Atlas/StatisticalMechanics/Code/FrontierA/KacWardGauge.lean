/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.KacWardTheta
import Code.Onsager.ShermanLoop

open scoped BigOperators

namespace StatMech.FrontierA

open Matrix


noncomputable def kwGaugeConjugate
    {D : Type*} [Fintype D] [DecidableEq D]
    (gauge : D -> ℂ) (M : Matrix D D ℂ) : Matrix D D ℂ :=
  fun i j => (gauge i)⁻¹ * M i j * gauge j


theorem kw_det_gaugeConjugate
    {D : Type*} [Fintype D] [DecidableEq D]
    (gauge : D -> ℂ) (M : Matrix D D ℂ)
    (hgauge : ∀ i, gauge i ≠ 0) :
    (kwGaugeConjugate gauge M).det = M.det := by
  rw [Matrix.det_apply, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro sigma _
  congr 1
  simp only [kwGaugeConjugate]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hgaugeProd : ∏ i, gauge i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => hgauge i)
  have hreindex : ∏ i, (gauge (sigma i))⁻¹ = (∏ i, gauge i)⁻¹ := by
    calc
      (∏ i, (gauge (sigma i))⁻¹) = ∏ i, (gauge i)⁻¹ :=
        Equiv.prod_comp sigma (fun i => (gauge i)⁻¹)
      _ = (∏ i, gauge i)⁻¹ := by
        exact Finset.prod_inv_distrib (s := Finset.univ) gauge
  rw [hreindex]
  calc
    (∏ i, gauge i)⁻¹ * (∏ i, M (sigma i) i) * ∏ i, gauge i =
        ((∏ i, gauge i)⁻¹ * ∏ i, gauge i) *
          ∏ i, M (sigma i) i := by ring
    _ = ∏ i, M (sigma i) i := by rw [inv_mul_cancel₀ hgaugeProd, one_mul]


theorem kwGaugeConjugate_one
    {D : Type*} [Fintype D] [DecidableEq D]
    (gauge : D -> ℂ) (hgauge : ∀ i, gauge i ≠ 0) :
    kwGaugeConjugate gauge (1 : Matrix D D ℂ) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [kwGaugeConjugate, hgauge i]
  · simp [kwGaugeConjugate, hij]


theorem kwGaugeConjugate_sub
    {D : Type*} [Fintype D] [DecidableEq D]
    (gauge : D -> ℂ) (M N : Matrix D D ℂ) :
    kwGaugeConjugate gauge (M - N) =
      kwGaugeConjugate gauge M - kwGaugeConjugate gauge N := by
  ext i j
  simp only [kwGaugeConjugate, Matrix.sub_apply]
  ring


theorem kw_det_one_sub_gaugeConjugate
    {D : Type*} [Fintype D] [DecidableEq D]
    (gauge : D -> ℂ) (M : Matrix D D ℂ)
    (hgauge : ∀ i, gauge i ≠ 0) :
    (1 - kwGaugeConjugate gauge M).det = (1 - M).det := by
  have hmatrix : 1 - kwGaugeConjugate gauge M =
      kwGaugeConjugate gauge (1 - M) := by
    rw [kwGaugeConjugate_sub, kwGaugeConjugate_one gauge hgauge]
  rw [hmatrix, kw_det_gaugeConjugate gauge _ hgauge]


theorem kw_loopWeight_gaugeConjugate
    {D : Type*} [Fintype D] [DecidableEq D]
    {n : ℕ} [NeZero n]
    (gauge : D -> ℂ) (M : Matrix D D ℂ)
    (hgauge : ∀ i, gauge i ≠ 0) (loop : Fin n -> D) :
    StatMech.Onsager.ons_loopWeight (kwGaugeConjugate gauge M) loop =
      StatMech.Onsager.ons_loopWeight M loop := by
  unfold StatMech.Onsager.ons_loopWeight kwGaugeConjugate
  simp_rw [mul_assoc]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib]
  have hreindex : (∏ k, gauge (loop (k + 1))) =
      ∏ k, gauge (loop k) :=
    Equiv.prod_comp (Equiv.addRight (1 : Fin n))
      (fun k => gauge (loop k))
  rw [hreindex]
  have hprod : (∏ k, gauge (loop k)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun k _ => hgauge (loop k))
  calc
    (∏ k, gauge (loop k))⁻¹ *
        ((∏ k, M (loop k) (loop (k + 1))) *
          ∏ k, gauge (loop k)) =
      ((∏ k, gauge (loop k))⁻¹ * ∏ k, gauge (loop k)) *
        ∏ k, M (loop k) (loop (k + 1)) := by ring
    _ = ∏ k, M (loop k) (loop (k + 1)) := by
      rw [inv_mul_cancel₀ hprod, one_mul]



theorem kacWard_theta_gauge
    (omega : ℂ) (homega : omega ≠ 0) (hI : omega ^ 2 = Complex.I)
    (x : Fin 3 -> ℂ) (gauge : (Fin 3 ⊕ Fin 3) -> ℂ)
    (hgauge : ∀ i, gauge i ≠ 0) :
    (1 - kwGaugeConjugate gauge (kwThetaTransition omega x)).det =
      (kwThetaEvenPolynomial x) ^ 2 := by
  rw [kw_det_one_sub_gaugeConjugate gauge _ hgauge]
  exact kacWard_theta omega homega hI x

end StatMech.FrontierA
