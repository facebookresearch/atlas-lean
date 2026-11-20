/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















import Code.Sharpness.BackboneSupportLexCounterexample
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

open Finset

namespace StatMech.Sharpness



noncomputable def shbEvenCurrentSeries (x : ℝ) : ℝ :=
  ∑' k : ℕ, x ^ (2 * k) / (2 * k).factorial



noncomputable def shbOddCurrentSeries (x : ℝ) : ℝ :=
  ∑' k : ℕ, x ^ (2 * k + 1) / (2 * k + 1).factorial

theorem shb_evenCurrentSeries_eq_cosh (x : ℝ) :
    shbEvenCurrentSeries x = Real.cosh x := by
  unfold shbEvenCurrentSeries
  exact (Real.cosh_eq_tsum x).symm

theorem shb_oddCurrentSeries_eq_sinh (x : ℝ) :
    shbOddCurrentSeries x = Real.sinh x := by
  unfold shbOddCurrentSeries
  exact (Real.sinh_eq_tsum x).symm


noncomputable def shbParitySeriesMass
    {E : Type*} [Fintype E] [DecidableEq E]
    (P : Finset E → Prop) [DecidablePred P] (x : ℝ) : ℝ :=
  ∑ A ∈ (Finset.univ : Finset E).powerset,
    if P A then
      ∏ e : E, if e ∈ A then shbOddCurrentSeries x else shbEvenCurrentSeries x
    else 0


def shbParityPolynomial
    {E : Type*} [Fintype E] [DecidableEq E]
    (P : Finset E → Prop) [DecidablePred P] (t : ℝ) : ℝ :=
  ∑ A ∈ (Finset.univ : Finset E).powerset,
    if P A then t ^ A.card else 0

private theorem shb_sinh_eq_cosh_mul_tanh (x : ℝ) :
    Real.sinh x = Real.cosh x * Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp



theorem shb_paritySeriesMass_eq_cosh_mul_polynomial
    {E : Type*} [Fintype E] [DecidableEq E]
    (P : Finset E → Prop) [DecidablePred P] (x : ℝ) :
    shbParitySeriesMass P x =
      Real.cosh x ^ Fintype.card E * shbParityPolynomial P (Real.tanh x) := by
  unfold shbParitySeriesMass shbParityPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hP : P A
  · rw [if_pos hP, if_pos hP]
    simp_rw [shb_evenCurrentSeries_eq_cosh, shb_oddCurrentSeries_eq_sinh,
      shb_sinh_eq_cosh_mul_tanh]
    rw [Finset.prod_ite]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_const]
    have hcard := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset E)) (fun e ↦ e ∈ A)
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.card_univ] at hcard
    rw [mul_pow]
    calc
      Real.cosh x ^ A.card * Real.tanh x ^ A.card *
            Real.cosh x ^ ((Finset.univ.filter fun e ↦ ¬ e ∈ A).card) =
          (Real.cosh x ^ A.card *
              Real.cosh x ^ ((Finset.univ.filter fun e ↦ ¬ e ∈ A).card)) *
            Real.tanh x ^ A.card := by ring
      _ = Real.cosh x ^
              (A.card + (Finset.univ.filter fun e ↦ ¬ e ∈ A).card) *
            Real.tanh x ^ A.card := by rw [pow_add]
      _ = Real.cosh x ^ Fintype.card E * Real.tanh x ^ A.card := by rw [hcard]
  · rw [if_neg hP, if_neg hP, mul_zero]


noncomputable def shbParitySeriesMassOn
    {E : Type*} [DecidableEq E] (S : Finset E)
    (P : Finset E → Prop) [DecidablePred P] (x : ℝ) : ℝ :=
  ∑ A ∈ S.powerset,
    if P A then
      ∏ e ∈ S, if e ∈ A then shbOddCurrentSeries x else shbEvenCurrentSeries x
    else 0


def shbParityPolynomialOn
    {E : Type*} [DecidableEq E] (S : Finset E)
    (P : Finset E → Prop) [DecidablePred P] (t : ℝ) : ℝ :=
  ∑ A ∈ S.powerset, if P A then t ^ A.card else 0


theorem shb_paritySeriesMassOn_eq_cosh_mul_polynomial
    {E : Type*} [DecidableEq E] (S : Finset E)
    (P : Finset E → Prop) [DecidablePred P] (x : ℝ) :
    shbParitySeriesMassOn S P x =
      Real.cosh x ^ S.card * shbParityPolynomialOn S P (Real.tanh x) := by
  unfold shbParitySeriesMassOn shbParityPolynomialOn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  by_cases hP : P A
  · rw [if_pos hP, if_pos hP]
    simp_rw [shb_evenCurrentSeries_eq_cosh, shb_oddCurrentSeries_eq_sinh,
      shb_sinh_eq_cosh_mul_tanh]
    rw [Finset.prod_ite]
    simp only [Finset.filter_mem_eq_inter, Finset.prod_const]
    have hsub : A ⊆ S := Finset.mem_powerset.mp hA
    rw [Finset.inter_eq_right.mpr hsub]
    have hcard := Finset.card_filter_add_card_filter_not
      (s := S) (fun e ↦ e ∈ A)
    simp only [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub] at hcard
    rw [mul_pow]
    calc
      Real.cosh x ^ A.card * Real.tanh x ^ A.card *
            Real.cosh x ^ ((S.filter fun e ↦ ¬ e ∈ A).card) =
          (Real.cosh x ^ A.card *
              Real.cosh x ^ ((S.filter fun e ↦ ¬ e ∈ A).card)) *
            Real.tanh x ^ A.card := by ring
      _ = Real.cosh x ^
              (A.card + (S.filter fun e ↦ ¬ e ∈ A).card) *
            Real.tanh x ^ A.card := by rw [pow_add]
      _ = Real.cosh x ^ S.card * Real.tanh x ^ A.card := by rw [hcard]
  · rw [if_neg hP, if_neg hP, mul_zero]


def shbK4DirectFiberPolynomial (E : Finset shbK4Edge) (t : ℝ) : ℝ :=
  ∑ A ∈ shbK4Configs E, if shbK4SelectsDirect03 A then t ^ A.card else 0


def shbK4VacuumPolynomial (E : Finset shbK4Edge) (t : ℝ) : ℝ :=
  ∑ A ∈ shbK4Configs E, if shbK4Boundary A = ∅ then t ^ A.card else 0

theorem shbK4DirectFiberMass_cast (E : Finset shbK4Edge) (t : ℚ) :
    (shbK4DirectFiberMass E t : ℝ) = shbK4DirectFiberPolynomial E t := by
  unfold shbK4DirectFiberMass shbK4DirectFiberPolynomial
  push_cast
  apply Finset.sum_congr rfl
  intro A hA
  by_cases h : shbK4SelectsDirect03 A <;> simp [h]

theorem shbK4VacuumMass_cast (E : Finset shbK4Edge) (t : ℚ) :
    (shbK4VacuumMass E t : ℝ) = shbK4VacuumPolynomial E t := by
  unfold shbK4VacuumMass shbK4VacuumPolynomial
  push_cast
  apply Finset.sum_congr rfl
  intro A hA
  by_cases h : shbK4Boundary A = ∅ <;> simp [h]


noncomputable def shbK4DirectRhoPolynomial (E : Finset shbK4Edge) (t : ℝ) : ℝ :=
  shbK4DirectFiberPolynomial E t / shbK4VacuumPolynomial E t

theorem shbK4DirectRho_cast (E : Finset shbK4Edge) (t : ℚ) :
    (shbK4DirectRho E t : ℝ) = shbK4DirectRhoPolynomial E t := by
  rw [shbK4DirectRho, shbK4DirectRhoPolynomial, Rat.cast_div,
    shbK4DirectFiberMass_cast, shbK4VacuumMass_cast]



theorem shb_supportLex_realParity_P3_counterexample :
    shbK4DirectRhoPolynomial shbK4H (2 / 3) <
      shbK4DirectRhoPolynomial shbK4G (2 / 3) := by
  have h := shb_supportLex_edgeDomain_P3_counterexample
  have hH := shbK4DirectRho_cast shbK4H (2 / 3)
  have hG := shbK4DirectRho_cast shbK4G (2 / 3)
  norm_num at hH hG
  rw [← hH, ← hG]
  exact_mod_cast h


theorem shb_tanh_artanh_two_thirds :
    Real.tanh (Real.artanh (2 / 3)) = (2 / 3 : ℝ) := by
  rw [Real.tanh_artanh]
  norm_num



noncomputable def shbK4DirectFiberSeriesMass
    (E : Finset shbK4Edge) (x : ℝ) : ℝ :=
  shbParitySeriesMassOn E shbK4SelectsDirect03 x


noncomputable def shbK4VacuumSeriesMass
    (E : Finset shbK4Edge) (x : ℝ) : ℝ :=
  shbParitySeriesMassOn E (fun A ↦ shbK4Boundary A = ∅) x

theorem shbK4DirectFiberSeriesMass_eq (E : Finset shbK4Edge) (x : ℝ) :
    shbK4DirectFiberSeriesMass E x =
      Real.cosh x ^ E.card * shbK4DirectFiberPolynomial E (Real.tanh x) := by
  exact shb_paritySeriesMassOn_eq_cosh_mul_polynomial
    E shbK4SelectsDirect03 x

theorem shbK4VacuumSeriesMass_eq (E : Finset shbK4Edge) (x : ℝ) :
    shbK4VacuumSeriesMass E x =
      Real.cosh x ^ E.card * shbK4VacuumPolynomial E (Real.tanh x) := by
  exact shb_paritySeriesMassOn_eq_cosh_mul_polynomial
    E (fun A ↦ shbK4Boundary A = ∅) x


noncomputable def shbK4DirectRhoSeries
    (E : Finset shbK4Edge) (x : ℝ) : ℝ :=
  shbK4DirectFiberSeriesMass E x / shbK4VacuumSeriesMass E x



theorem shbK4DirectRhoSeries_eq_polynomial
    (E : Finset shbK4Edge) (x : ℝ) :
    shbK4DirectRhoSeries E x =
      shbK4DirectRhoPolynomial E (Real.tanh x) := by
  rw [shbK4DirectRhoSeries, shbK4DirectFiberSeriesMass_eq,
    shbK4VacuumSeriesMass_eq, shbK4DirectRhoPolynomial]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (Real.cosh_pos x).ne')




theorem shb_supportLex_series_P3_counterexample :
    shbK4DirectRhoSeries shbK4H (Real.artanh (2 / 3)) <
      shbK4DirectRhoSeries shbK4G (Real.artanh (2 / 3)) := by
  rw [shbK4DirectRhoSeries_eq_polynomial,
    shbK4DirectRhoSeries_eq_polynomial, shb_tanh_artanh_two_thirds]
  exact shb_supportLex_realParity_P3_counterexample

end StatMech.Sharpness
