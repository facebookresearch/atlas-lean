/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.ClassicalOrthogonalPolynomial
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.Basic.ENNReal.Real
import Mathlib.Tactic

namespace MetaMathlibExt

open MeasureTheory Set Real

open scoped NNReal

example (F : ClassicalOrthogonalPolynomialFamily) (n : ℕ) : (F.P n).Monic :=
  F.monic n
example (F : ClassicalOrthogonalPolynomialFamily) (n : ℕ) : (F.P n).natDegree = n :=
  F.natDegree_eq n
example (F : ClassicalOrthogonalPolynomialFamily) (m n : ℕ) (h : m ≠ n) :
    MeasureTheory.integral F.μ
      (fun x => Polynomial.eval x (F.P m) * Polynomial.eval x (F.P n)) = 0 :=
  F.orthogonal m n h
example (F : ClassicalOrthogonalPolynomialFamily) (n : ℕ) :
    MeasureTheory.integral F.μ (fun x => (Polynomial.eval x (F.P n)) ^ 2) ≠ 0 :=
  F.norm_ne_zero n
example (F : ClassicalOrthogonalPolynomialFamily) :
    F.μ = (MeasureTheory.volume.restrict F.domain).withDensity
      (fun x => ENNReal.ofReal (F.weight x)) := F.measure_eq
example (F : ClassicalOrthogonalPolynomialFamily) : Set.OrdConnected F.domain :=
  F.ordConnected_domain
example (F : ClassicalOrthogonalPolynomialFamily) : (interior F.domain).Nonempty :=
  F.interior_domain_nonempty
example (F : ClassicalOrthogonalPolynomialFamily) :
    ∃ u0 u1 v0 v1 v2 : ℝ, (v0 ≠ 0 ∨ v1 ≠ 0 ∨ v2 ≠ 0) ∧
      ∀ x : ℝ, x ∈ interior F.domain →
        DifferentiableAt ℝ F.weight x ∧
          (v0 + v1 * x + v2 * x ^ 2) * deriv F.weight x =
            (u0 + u1 * x) * F.weight x :=
  F.classical

private noncomputable def monicChebyshev (n : ℕ) : Polynomial ℝ :=
  Polynomial.Chebyshev.T ℝ n *
    Polynomial.C (Polynomial.leadingCoeff (Polynomial.Chebyshev.T ℝ n))⁻¹

private theorem monicChebyshev_monic (n : ℕ) : (monicChebyshev n).Monic := by
  exact Polynomial.monic_mul_leadingCoeff_inv (Polynomial.Chebyshev.T_ne_zero ℝ n)

private theorem monicChebyshev_natDegree (n : ℕ) : (monicChebyshev n).natDegree = n := by
  rw [monicChebyshev, Polynomial.natDegree_mul_C]
  · simp
  · rw [Polynomial.Chebyshev.leadingCoeff_T]
    exact inv_ne_zero (pow_ne_zero _ (by norm_num))

private theorem monicChebyshev_orthogonal (m n : ℕ) (h : m ≠ n) :
    ∫ x, Polynomial.eval x (monicChebyshev m) * Polynomial.eval x (monicChebyshev n)
      ∂Polynomial.Chebyshev.measureT = 0 := by
  have hbase := Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne h
  calc
    ∫ x, Polynomial.eval x (monicChebyshev m) * Polynomial.eval x (monicChebyshev n)
        ∂Polynomial.Chebyshev.measureT =
        ((Polynomial.Chebyshev.T ℝ m).leadingCoeff⁻¹ *
          (Polynomial.Chebyshev.T ℝ n).leadingCoeff⁻¹) *
          ∫ x, (Polynomial.Chebyshev.T ℝ m).eval x *
            (Polynomial.Chebyshev.T ℝ n).eval x ∂Polynomial.Chebyshev.measureT := by
      simp only [monicChebyshev, Polynomial.eval_mul, Polynomial.eval_C]
      rw [← MeasureTheory.integral_const_mul]
      congr with x
      ring
    _ = 0 := by rw [hbase, mul_zero]

private theorem monicChebyshev_norm_ne_zero (n : ℕ) :
    ∫ x, (Polynomial.eval x (monicChebyshev n)) ^ 2
      ∂Polynomial.Chebyshev.measureT ≠ 0 := by
  have hc : (Polynomial.Chebyshev.T ℝ n).leadingCoeff⁻¹ ≠ 0 := by
    rw [Polynomial.Chebyshev.leadingCoeff_T]
    exact inv_ne_zero (pow_ne_zero _ (by norm_num))
  rw [show (∫ x, (Polynomial.eval x (monicChebyshev n)) ^ 2
      ∂Polynomial.Chebyshev.measureT) =
      (Polynomial.Chebyshev.T ℝ n).leadingCoeff⁻¹ ^ 2 *
        ∫ x, (Polynomial.Chebyshev.T ℝ n).eval x *
          (Polynomial.Chebyshev.T ℝ n).eval x ∂Polynomial.Chebyshev.measureT by
    rw [← MeasureTheory.integral_const_mul]
    congr with x
    simp [monicChebyshev, pow_two]
    ring]
  apply mul_ne_zero (pow_ne_zero _ hc)
  by_cases hn : n = 0
  · subst n
    have hzero :
        (∫ x, (Polynomial.Chebyshev.T ℝ (0 : ℕ)).eval x *
          (Polynomial.Chebyshev.T ℝ (0 : ℕ)).eval x
            ∂Polynomial.Chebyshev.measureT) = Real.pi := by
      simpa using Polynomial.Chebyshev.integral_eval_T_real_mul_self_measureT_zero
    rw [hzero]
    exact Real.pi_ne_zero
  · rw [Polynomial.Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero hn]
    exact div_ne_zero Real.pi_ne_zero (by norm_num)

private noncomputable def chebyshevWeight : ℝ → ℝ :=
  (fun x : ℝ => Real.sqrt (1 - x ^ 2))⁻¹

private noncomputable def chebyshevMeasure : MeasureTheory.Measure ℝ :=
  (MeasureTheory.volume.restrict (Set.Ioc (-1) 1)).withDensity
    (fun x => ENNReal.ofReal (chebyshevWeight x))

private theorem chebyshevWeight_nonneg (x : ℝ) : 0 ≤ chebyshevWeight x := by
  change 0 ≤ (Real.sqrt (1 - x ^ 2))⁻¹
  exact inv_nonneg.mpr (Real.sqrt_nonneg _)

private theorem integral_chebyshevMeasure (f : ℝ → ℝ) :
    ∫ x, f x ∂chebyshevMeasure = ∫ x, f x ∂Polynomial.Chebyshev.measureT := by
  rw [Polynomial.Chebyshev.integral_measureT]
  unfold chebyshevMeasure
  rw [intervalIntegral.integral_of_le (by norm_num)]
  let wnn : ℝ → ℝ≥0 := fun x =>
    ⟨Real.sqrt (1 - x ^ 2)⁻¹, by positivity⟩
  have hdensity : (fun x => ENNReal.ofReal (chebyshevWeight x)) =
      (fun x => (wnn x : ENNReal)) := by
    funext x
    simp only [chebyshevWeight, Pi.inv_apply, wnn, Real.sqrt_inv]
    exact ENNReal.ofReal_eq_coe_nnreal (inv_nonneg.mpr (Real.sqrt_nonneg _))
  rw [hdensity]
  rw [integral_withDensity_eq_integral_smul (by fun_prop)]
  congr! 2 with x
  rw [NNReal.smul_def]
  change Real.sqrt (1 - x ^ 2)⁻¹ * f x = f x * Real.sqrt (1 - x ^ 2)⁻¹
  exact mul_comm _ _

private theorem monicChebyshev_orthogonal_explicit (m n : ℕ) (h : m ≠ n) :
    ∫ x, Polynomial.eval x (monicChebyshev m) * Polynomial.eval x (monicChebyshev n)
      ∂chebyshevMeasure = 0 := by
  rw [integral_chebyshevMeasure]
  exact monicChebyshev_orthogonal m n h

private theorem monicChebyshev_norm_ne_zero_explicit (n : ℕ) :
    ∫ x, (Polynomial.eval x (monicChebyshev n)) ^ 2 ∂chebyshevMeasure ≠ 0 := by
  rw [integral_chebyshevMeasure]
  exact monicChebyshev_norm_ne_zero n

private theorem chebyshevWeight_classical : ∃ u0 u1 v0 v1 v2 : ℝ,
    (v0 ≠ 0 ∨ v1 ≠ 0 ∨ v2 ≠ 0) ∧
      ∀ x : ℝ, x ∈ interior (Set.Ioc (-1) 1) →
        DifferentiableAt ℝ chebyshevWeight x ∧
          (v0 + v1 * x + v2 * x ^ 2) * deriv chebyshevWeight x =
            (u0 + u1 * x) * chebyshevWeight x := by
  refine ⟨0, 1, 1, 0, -1, by norm_num, ?_⟩
  intro x hx
  have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := by simpa using hx
  have hs : 0 < 1 - x ^ 2 := by
    rcases hx' with ⟨hxlo, hxhi⟩
    nlinarith
  have hquad : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    simpa only [Nat.reduceSub, pow_one, Nat.cast_ofNat, neg_mul] using
      (hasDerivAt_pow 2 x).const_sub 1
  have hsqrt := hquad.sqrt (ne_of_gt hs)
  have hsqrt_ne : Real.sqrt (1 - x ^ 2) ≠ 0 := Real.sqrt_ne_zero'.mpr hs
  have hinv := hsqrt.inv hsqrt_ne
  have hdiff : DifferentiableAt ℝ chebyshevWeight x := by
    simpa only [chebyshevWeight] using hinv.differentiableAt
  have hderiv : deriv chebyshevWeight x =
      -(-2 * x / (2 * Real.sqrt (1 - x ^ 2))) /
        (Real.sqrt (1 - x ^ 2)) ^ 2 := by
    simpa only [chebyshevWeight] using hinv.deriv
  refine ⟨hdiff, ?_⟩
  rw [hderiv]
  simp only [zero_add, one_mul, zero_mul, add_zero, neg_one_mul, chebyshevWeight,
    Pi.inv_apply]
  field_simp
  rw [Real.sq_sqrt hs.le]
  ring

private noncomputable def chebyshevFamily : ClassicalOrthogonalPolynomialFamily where
  P := monicChebyshev
  monic := monicChebyshev_monic
  natDegree_eq := monicChebyshev_natDegree
  μ := chebyshevMeasure
  domain := Set.Ioc (-1) 1
  measurable_domain := measurableSet_Ioc
  ordConnected_domain := ordConnected_Ioc
  interior_domain_nonempty := by
    rw [interior_Ioc]
    exact ⟨0, by norm_num⟩
  orthogonal := monicChebyshev_orthogonal_explicit
  norm_ne_zero := monicChebyshev_norm_ne_zero_explicit
  weight := chebyshevWeight
  weight_nonneg := fun x _ => chebyshevWeight_nonneg x
  measure_eq := rfl
  classical := chebyshevWeight_classical

example : (chebyshevFamily.P 4).Monic := chebyshevFamily.monic 4

example : (chebyshevFamily.P 4).natDegree = 4 := chebyshevFamily.natDegree_eq 4

example : chebyshevFamily.weight 0 = 1 := by
  norm_num [chebyshevFamily, chebyshevWeight]

end MetaMathlibExt
